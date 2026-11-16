#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <exception>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;
constexpr std::uint32_t kSeed = 0x5EED2026u;
constexpr int kWarmups = 1;
constexpr std::array<int, 4> kFullSizes{{1000, 10000, 100000, 1000000}};
volatile std::uint64_t gObservableChecksum = 0;

struct OperationStats {
    std::uint64_t rotations = 0;
    std::uint64_t recolorings = 0;
    std::uint64_t visitedNodes = 0;
};

struct TreeCounters {
    OperationStats totals;
    OperationStats current;
};

template <bool CountOperations>
class RBTreeImpl {
public:
    enum class Color : std::uint8_t { Red, Black };

    struct Node {
        int key = 0;
        int value = 0;
        Color color = Color::Black;
        Node* parent = nullptr;
        Node* left = nullptr;
        Node* right = nullptr;
    };

    RBTreeImpl() {
        nil_.color = Color::Black;
        nil_.parent = nil_.left = nil_.right = &nil_;
        root_ = &nil_;
    }

    RBTreeImpl(const RBTreeImpl&) = delete;
    RBTreeImpl& operator=(const RBTreeImpl&) = delete;

    ~RBTreeImpl() {
        clear(root_);
    }

    void beginOperation() {
        if constexpr (CountOperations) {
            counters_.current = {};
        }
    }

    OperationStats operationStats() const {
        if constexpr (CountOperations) {
            return counters_.current;
        }
        return {};
    }

    OperationStats totalStats() const {
        if constexpr (CountOperations) {
            return counters_.totals;
        }
        return {};
    }

    bool emplace(int key, int value) {
        Node* parent = &nil_;
        Node* current = root_;
        while (current != &nil_) {
            visit(current);
            parent = current;
            if (key == current->key) {
                return false;
            }
            current = key < current->key ? current->left : current->right;
        }

        Node* node = new Node{key, value, Color::Red, parent, &nil_, &nil_};
        if (parent == &nil_) {
            root_ = node;
        } else if (key < parent->key) {
            parent->left = node;
        } else {
            parent->right = node;
        }
        ++size_;
        insertFixup(node);
        return true;
    }

    Node* findNode(int key) {
        Node* current = root_;
        while (current != &nil_) {
            visit(current);
            if (key == current->key) {
                return current;
            }
            current = key < current->key ? current->left : current->right;
        }
        return nullptr;
    }

    const Node* lowerBoundFind(int key) {
        Node* current = root_;
        Node* candidate = &nil_;
        while (current != &nil_) {
            visit(current);
            if (current->key >= key) {
                candidate = current;
                current = current->left;
            } else {
                current = current->right;
            }
        }
        return candidate != &nil_ && candidate->key == key ? candidate : nullptr;
    }

    bool erase(int key) {
        Node* target = root_;
        while (target != &nil_) {
            visit(target);
            if (key == target->key) {
                break;
            }
            target = key < target->key ? target->left : target->right;
        }
        if (target == &nil_) {
            return false;
        }

        Node* moved = target;
        Color originalColor = moved->color;
        Node* fixNode = nullptr;
        if (target->left == &nil_) {
            fixNode = target->right;
            transplant(target, target->right);
        } else if (target->right == &nil_) {
            fixNode = target->left;
            transplant(target, target->left);
        } else {
            moved = minimum(target->right);
            originalColor = moved->color;
            fixNode = moved->right;
            if (moved->parent == target) {
                fixNode->parent = moved;
            } else {
                transplant(moved, moved->right);
                moved->right = target->right;
                moved->right->parent = moved;
            }
            transplant(target, moved);
            moved->left = target->left;
            moved->left->parent = moved;
            setColor(moved, target->color);
        }

        delete target;
        --size_;
        if (originalColor == Color::Black) {
            deleteFixup(fixNode);
        }
        if (root_ != &nil_) {
            root_->parent = &nil_;
        }
        nil_.parent = &nil_;
        return true;
    }

    std::size_t size() const { return size_; }

    std::size_t height() const {
        return heightOf(root_);
    }

    bool validate(std::string& error) const {
        if (nil_.color != Color::Black || nil_.left != &nil_ ||
            nil_.right != &nil_) {
            error = "the NIL sentinel is not black/self-linked";
            return false;
        }
        if (root_ == &nil_) {
            if (size_ != 0) {
                error = "empty root but nonzero size";
                return false;
            }
            return true;
        }
        if (root_->parent != &nil_) {
            error = "root parent is not NIL";
            return false;
        }
        if (root_->color != Color::Black) {
            error = "root is not black";
            return false;
        }

        std::size_t counted = 0;
        int previous = 0;
        bool havePrevious = false;
        int blackHeight = 0;
        if (!validateNode(root_, &nil_, counted, previous, havePrevious,
                          blackHeight, error)) {
            return false;
        }
        if (counted != size_) {
            error = "stored size differs from reachable node count";
            return false;
        }
        return true;
    }

private:
    Node nil_{};
    Node* root_ = nullptr;
    std::size_t size_ = 0;
    TreeCounters counters_{};

    void visit(Node*) {
        if constexpr (CountOperations) {
            ++counters_.current.visitedNodes;
            ++counters_.totals.visitedNodes;
        }
    }

    void noteRotation() {
        if constexpr (CountOperations) {
            ++counters_.current.rotations;
            ++counters_.totals.rotations;
        }
    }

    void setColor(Node* node, Color color) {
        if (node == &nil_ || node->color == color) {
            return;
        }
        node->color = color;
        if constexpr (CountOperations) {
            ++counters_.current.recolorings;
            ++counters_.totals.recolorings;
        }
    }

    void rotateLeft(Node* pivot) {
        Node* child = pivot->right;
        pivot->right = child->left;
        if (child->left != &nil_) {
            child->left->parent = pivot;
        }
        child->parent = pivot->parent;
        if (pivot->parent == &nil_) {
            root_ = child;
        } else if (pivot == pivot->parent->left) {
            pivot->parent->left = child;
        } else {
            pivot->parent->right = child;
        }
        child->left = pivot;
        pivot->parent = child;
        noteRotation();
    }

    void rotateRight(Node* pivot) {
        Node* child = pivot->left;
        pivot->left = child->right;
        if (child->right != &nil_) {
            child->right->parent = pivot;
        }
        child->parent = pivot->parent;
        if (pivot->parent == &nil_) {
            root_ = child;
        } else if (pivot == pivot->parent->right) {
            pivot->parent->right = child;
        } else {
            pivot->parent->left = child;
        }
        child->right = pivot;
        pivot->parent = child;
        noteRotation();
    }

    void insertFixup(Node* node) {
        while (node->parent->color == Color::Red) {
            if (node->parent == node->parent->parent->left) {
                Node* uncle = node->parent->parent->right;
                if (uncle->color == Color::Red) {
                    setColor(node->parent, Color::Black);
                    setColor(uncle, Color::Black);
                    setColor(node->parent->parent, Color::Red);
                    node = node->parent->parent;
                } else {
                    if (node == node->parent->right) {
                        node = node->parent;
                        rotateLeft(node);
                    }
                    setColor(node->parent, Color::Black);
                    setColor(node->parent->parent, Color::Red);
                    rotateRight(node->parent->parent);
                }
            } else {
                Node* uncle = node->parent->parent->left;
                if (uncle->color == Color::Red) {
                    setColor(node->parent, Color::Black);
                    setColor(uncle, Color::Black);
                    setColor(node->parent->parent, Color::Red);
                    node = node->parent->parent;
                } else {
                    if (node == node->parent->left) {
                        node = node->parent;
                        rotateRight(node);
                    }
                    setColor(node->parent, Color::Black);
                    setColor(node->parent->parent, Color::Red);
                    rotateLeft(node->parent->parent);
                }
            }
        }
        setColor(root_, Color::Black);
    }

    void transplant(Node* oldNode, Node* newNode) {
        if (oldNode->parent == &nil_) {
            root_ = newNode;
        } else if (oldNode == oldNode->parent->left) {
            oldNode->parent->left = newNode;
        } else {
            oldNode->parent->right = newNode;
        }
        newNode->parent = oldNode->parent;
    }

    Node* minimum(Node* node) {
        visit(node);
        while (node->left != &nil_) {
            node = node->left;
            visit(node);
        }
        return node;
    }

    void deleteFixup(Node* node) {
        while (node != root_ && node->color == Color::Black) {
            if (node == node->parent->left) {
                Node* sibling = node->parent->right;
                if (sibling->color == Color::Red) {
                    setColor(sibling, Color::Black);
                    setColor(node->parent, Color::Red);
                    rotateLeft(node->parent);
                    sibling = node->parent->right;
                }
                if (sibling->left->color == Color::Black &&
                    sibling->right->color == Color::Black) {
                    setColor(sibling, Color::Red);
                    node = node->parent;
                } else {
                    if (sibling->right->color == Color::Black) {
                        setColor(sibling->left, Color::Black);
                        setColor(sibling, Color::Red);
                        rotateRight(sibling);
                        sibling = node->parent->right;
                    }
                    setColor(sibling, node->parent->color);
                    setColor(node->parent, Color::Black);
                    setColor(sibling->right, Color::Black);
                    rotateLeft(node->parent);
                    node = root_;
                }
            } else {
                Node* sibling = node->parent->left;
                if (sibling->color == Color::Red) {
                    setColor(sibling, Color::Black);
                    setColor(node->parent, Color::Red);
                    rotateRight(node->parent);
                    sibling = node->parent->left;
                }
                if (sibling->right->color == Color::Black &&
                    sibling->left->color == Color::Black) {
                    setColor(sibling, Color::Red);
                    node = node->parent;
                } else {
                    if (sibling->left->color == Color::Black) {
                        setColor(sibling->right, Color::Black);
                        setColor(sibling, Color::Red);
                        rotateLeft(sibling);
                        sibling = node->parent->left;
                    }
                    setColor(sibling, node->parent->color);
                    setColor(node->parent, Color::Black);
                    setColor(sibling->left, Color::Black);
                    rotateRight(node->parent);
                    node = root_;
                }
            }
        }
        setColor(node, Color::Black);
    }

    std::size_t heightOf(Node* node) const {
        if (node == &nil_) {
            return 0;
        }
        return 1 + std::max(heightOf(node->left), heightOf(node->right));
    }

    bool validateNode(const Node* node, const Node* expectedParent,
                      std::size_t& counted,
                      int& previous, bool& havePrevious, int& blackHeight,
                      std::string& error) const {
        if (node == &nil_) {
            blackHeight = 1;
            return true;
        }
        if (node->parent != expectedParent) {
            error = "child parent pointer is inconsistent";
            return false;
        }
        ++counted;
        if (node->color == Color::Red &&
            (node->left->color != Color::Black ||
             node->right->color != Color::Black)) {
            error = "red node has a red child";
            return false;
        }

        int leftBlackHeight = 0;
        int rightBlackHeight = 0;
        if (!validateNode(node->left, node, counted, previous, havePrevious,
                          leftBlackHeight, error)) {
            return false;
        }
        if (havePrevious && previous >= node->key) {
            error = "in-order keys are not strictly increasing";
            return false;
        }
        previous = node->key;
        havePrevious = true;
        if (!validateNode(node->right, node, counted, previous, havePrevious,
                          rightBlackHeight, error)) {
            return false;
        }
        if (leftBlackHeight != rightBlackHeight) {
            error = "black heights differ";
            return false;
        }
        blackHeight = leftBlackHeight + (node->color == Color::Black ? 1 : 0);
        return true;
    }

    void clear(Node* node) {
        if (node == &nil_) {
            return;
        }
        clear(node->left);
        clear(node->right);
        delete node;
    }
};

using RBTree = RBTreeImpl<false>;
using InstrumentedRBTree = RBTreeImpl<true>;

struct CountingCompare {
    std::uint64_t* calls = nullptr;

    bool operator()(int left, int right) const {
        ++*calls;
        return left < right;
    }
};

struct Dataset {
    std::string workload;
    std::vector<int> insertKeys;
    std::vector<int> queries;
    std::array<std::vector<int>, 2> eraseOrders;
};

void require(bool condition, const std::string& message) {
    if (!condition) {
        throw std::runtime_error(message);
    }
}

void validateOrThrow(const RBTree& tree, const std::string& context) {
    std::string error;
    if (!tree.validate(error)) {
        throw std::runtime_error(context + ": " + error);
    }
}

void validateOrThrow(const InstrumentedRBTree& tree,
                     const std::string& context) {
    std::string error;
    if (!tree.validate(error)) {
        throw std::runtime_error(context + ": " + error);
    }
}

std::uint32_t mixedSeed(std::uint32_t salt, int n) {
    return kSeed ^ salt ^ (static_cast<std::uint32_t>(n) * 2654435761u);
}

Dataset makeDataset(int n, int workloadIndex) {
    Dataset data;
    data.workload = workloadIndex == 0 ? "sorted"
                    : workloadIndex == 1 ? "random"
                                         : "semi_sorted_10pct_swaps";
    data.insertKeys.resize(static_cast<std::size_t>(n));
    std::iota(data.insertKeys.begin(), data.insertKeys.end(), 0);

    if (workloadIndex == 1) {
        std::mt19937 generator(mixedSeed(0x100u, n));
        std::shuffle(data.insertKeys.begin(), data.insertKeys.end(), generator);
    } else if (workloadIndex == 2) {
        std::mt19937 generator(mixedSeed(0x200u, n));
        const int swaps = n / 10;
        std::uniform_int_distribution<int> position(0, n - 1);
        for (int i = 0; i < swaps; ++i) {
            std::swap(data.insertKeys[static_cast<std::size_t>(position(generator))],
                      data.insertKeys[static_cast<std::size_t>(position(generator))]);
        }
    }

    data.queries.resize(static_cast<std::size_t>(n));
    std::iota(data.queries.begin(), data.queries.end(), 0);
    std::mt19937 queryGenerator(mixedSeed(0x300u, n));
    std::shuffle(data.queries.begin(), data.queries.end(), queryGenerator);

    for (std::size_t order = 0; order < data.eraseOrders.size(); ++order) {
        data.eraseOrders[order].resize(static_cast<std::size_t>(n));
        std::iota(data.eraseOrders[order].begin(),
                  data.eraseOrders[order].end(), 0);
        std::mt19937 eraseGenerator(
            mixedSeed(0x400u + static_cast<std::uint32_t>(order), n));
        std::shuffle(data.eraseOrders[order].begin(),
                     data.eraseOrders[order].end(), eraseGenerator);
    }
    return data;
}

template <typename Tree>
void populateTree(Tree& tree, const std::vector<int>& keys) {
    for (int key : keys) {
        tree.emplace(key, key);
    }
}

void populateMap(std::map<int, int>& values, const std::vector<int>& keys) {
    for (int key : keys) {
        values.emplace(key, key);
    }
}

struct TimedSample {
    std::int64_t elapsedNs = 0;
    std::uint64_t checksum = 0;
};

template <typename Function>
TimedSample timeOperations(Function&& function) {
    const auto start = Clock::now();
    const std::uint64_t checksum = function();
    const auto finish = Clock::now();
    gObservableChecksum = gObservableChecksum ^ checksum;
    return {std::chrono::duration_cast<std::chrono::nanoseconds>(
                finish - start).count(),
            checksum};
}

TimedSample timeRBInsert(const std::vector<int>& keys) {
    RBTree tree;
    TimedSample sample = timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : keys) {
            checksum += tree.emplace(key, key);
        }
        return checksum;
    });
    validateOrThrow(tree, "RBTree after timed insertion");
    require(tree.size() == keys.size(), "RBTree insertion size mismatch");
    return sample;
}

TimedSample timeMapInsert(const std::vector<int>& keys) {
    std::map<int, int> values;
    TimedSample sample = timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : keys) {
            checksum += values.emplace(key, key).second;
        }
        return checksum;
    });
    require(values.size() == keys.size(), "std::map insertion size mismatch");
    return sample;
}

TimedSample timeRBSearch(const Dataset& data) {
    RBTree tree;
    populateTree(tree, data.insertKeys);
    validateOrThrow(tree, "RBTree before timed search");
    return timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : data.queries) {
            const RBTree::Node* found = tree.findNode(key);
            if (found != nullptr) {
                checksum += static_cast<std::uint64_t>(found->key) +
                            static_cast<std::uint64_t>(found->value) + 1;
            }
        }
        return checksum;
    });
}

TimedSample timeMapSearch(const Dataset& data) {
    std::map<int, int> values;
    populateMap(values, data.insertKeys);
    return timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : data.queries) {
            const auto found = values.find(key);
            if (found != values.end()) {
                checksum += static_cast<std::uint64_t>(found->first) +
                            static_cast<std::uint64_t>(found->second) + 1;
            }
        }
        return checksum;
    });
}

TimedSample timeRBErase(const Dataset& data, std::size_t order) {
    RBTree tree;
    populateTree(tree, data.insertKeys);
    validateOrThrow(tree, "RBTree before timed deletion");
    TimedSample sample = timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : data.eraseOrders[order]) {
            checksum += tree.erase(key);
        }
        return checksum;
    });
    validateOrThrow(tree, "RBTree after timed deletion");
    require(tree.size() == 0, "RBTree deletion did not empty the tree");
    return sample;
}

TimedSample timeMapErase(const Dataset& data, std::size_t order) {
    std::map<int, int> values;
    populateMap(values, data.insertKeys);
    TimedSample sample = timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : data.eraseOrders[order]) {
            checksum += values.erase(key);
        }
        return checksum;
    });
    require(values.empty(), "std::map deletion did not empty the map");
    return sample;
}

struct RawRow {
    std::string workload;
    int n = 0;
    std::string operation;
    int eraseOrder = 0;
    int repetition = 0;
    std::string structure;
    TimedSample sample;
};

struct MedianRow {
    std::string workload;
    int n = 0;
    std::string operation;
    int eraseOrder = 0;
    std::string structure;
    double medianElapsedNs = 0;
    double medianNsPerOperation = 0;
};

double median(std::vector<double> values) {
    std::sort(values.begin(), values.end());
    const std::size_t middle = values.size() / 2;
    if (values.size() % 2 != 0) {
        return values[middle];
    }
    return (values[middle - 1] + values[middle]) / 2.0;
}

std::string csvQuote(const std::string& value) {
    if (value.find_first_of(",\"\r\n") == std::string::npos) {
        return value;
    }
    std::string quoted = "\"";
    for (char c : value) {
        if (c == '"') {
            quoted += '"';
        }
        quoted += c;
    }
    return quoted + '"';
}

struct StructureRow {
    std::string workload;
    int n = 0;
    std::string operation;
    int eraseOrder = 0;
    std::string structure;
    std::size_t height = 0;
    std::uint64_t rotations = 0;
    double rotationsPerOperation = 0;
    std::uint64_t maxRotations = 0;
    std::uint64_t recolorings = 0;
    double recoloringsPerOperation = 0;
    std::uint64_t maxRecolorings = 0;
    std::uint64_t visitedOrComparisons = 0;
    double visitedOrComparisonsPerOperation = 0;
    std::uint64_t maxVisitedOrComparisons = 0;
};

struct AccumulatedStats {
    std::uint64_t rotations = 0;
    std::uint64_t recolorings = 0;
    std::uint64_t visits = 0;
    std::uint64_t maxRotations = 0;
    std::uint64_t maxRecolorings = 0;
    std::uint64_t maxVisits = 0;

    void add(const OperationStats& stats) {
        rotations += stats.rotations;
        recolorings += stats.recolorings;
        visits += stats.visitedNodes;
        maxRotations = std::max(maxRotations, stats.rotations);
        maxRecolorings = std::max(maxRecolorings, stats.recolorings);
        maxVisits = std::max(maxVisits, stats.visitedNodes);
    }
};

std::vector<StructureRow> collectStructureStats(const Dataset& data) {
    const int n = static_cast<int>(data.insertKeys.size());
    std::vector<StructureRow> rows;

    InstrumentedRBTree tree;
    AccumulatedStats insertStats;
    for (int key : data.insertKeys) {
        tree.beginOperation();
        require(tree.emplace(key, key), "duplicate key in insertion data");
        insertStats.add(tree.operationStats());
    }
    validateOrThrow(tree, "instrumented tree after insertion");
    const std::size_t height = tree.height();

    std::uint64_t insertComparisons = 0;
    std::map<int, int, CountingCompare> countedMap(
        CountingCompare{&insertComparisons});
    for (int key : data.insertKeys) {
        countedMap.emplace(key, key);
    }
    rows.push_back({"", n, "insert", 0, "RBTree", height,
                    insertStats.rotations,
                    static_cast<double>(insertStats.rotations) / n,
                    insertStats.maxRotations, insertStats.recolorings,
                    static_cast<double>(insertStats.recolorings) / n,
                    insertStats.maxRecolorings, insertStats.visits,
                    static_cast<double>(insertStats.visits) / n,
                    insertStats.maxVisits});
    rows.push_back({"", n, "insert", 0, "std::map", height, 0, 0, 0, 0, 0,
                    0, insertComparisons,
                    static_cast<double>(insertComparisons) / n, 0});

    AccumulatedStats searchStats;
    for (int key : data.queries) {
        tree.beginOperation();
        require(tree.findNode(key) != nullptr,
                "expected key missing in instrumented search");
        searchStats.add(tree.operationStats());
    }
    std::uint64_t searchComparisons = 0;
    std::map<int, int, CountingCompare> searchMap(
        CountingCompare{&searchComparisons});
    for (int key : data.insertKeys) {
        searchMap.emplace(key, key);
    }
    searchComparisons = 0;
    for (int key : data.queries) {
        require(searchMap.find(key) != searchMap.end(),
                "expected key missing in counted map search");
    }
    rows.push_back({"", n, "find", 0, "RBTree", height, 0, 0, 0, 0, 0, 0,
                    searchStats.visits,
                    static_cast<double>(searchStats.visits) / n,
                    searchStats.maxVisits});
    rows.push_back({"", n, "find", 0, "std::map", height, 0, 0, 0, 0, 0,
                    0, searchComparisons,
                    static_cast<double>(searchComparisons) / n, 0});

    for (std::size_t order = 0; order < data.eraseOrders.size(); ++order) {
        InstrumentedRBTree deleteTree;
        populateTree(deleteTree, data.insertKeys);
        deleteTree.beginOperation();
        AccumulatedStats deleteStats;
        for (int key : data.eraseOrders[order]) {
            deleteTree.beginOperation();
            require(deleteTree.erase(key), "expected key missing in deletion");
            deleteStats.add(deleteTree.operationStats());
        }
        validateOrThrow(deleteTree, "instrumented tree after deletion");
        require(deleteTree.size() == 0, "instrumented deletion left nodes");

        std::uint64_t eraseComparisons = 0;
        std::map<int, int, CountingCompare> eraseMap(
            CountingCompare{&eraseComparisons});
        for (int key : data.insertKeys) {
            eraseMap.emplace(key, key);
        }
        eraseComparisons = 0;
        for (int key : data.eraseOrders[order]) {
            require(eraseMap.erase(key) == 1,
                    "expected key missing in counted map deletion");
        }
        rows.push_back({"", n, "erase", static_cast<int>(order + 1),
                        "RBTree", height, deleteStats.rotations,
                        static_cast<double>(deleteStats.rotations) / n,
                        deleteStats.maxRotations, deleteStats.recolorings,
                        static_cast<double>(deleteStats.recolorings) / n,
                        deleteStats.maxRecolorings, deleteStats.visits,
                        static_cast<double>(deleteStats.visits) / n,
                        deleteStats.maxVisits});
        rows.push_back({"", n, "erase", static_cast<int>(order + 1),
                        "std::map", height, 0, 0, 0, 0, 0, 0,
                        eraseComparisons,
                        static_cast<double>(eraseComparisons) / n, 0});
    }
    for (auto& row : rows) {
        row.workload = data.workload;
    }
    return rows;
}

template <typename RBFunction, typename MapFunction>
void runTimedGroup(const Dataset& data, const std::string& operation,
                   int eraseOrder, int repetitions, int workloadIndex,
                   std::vector<RawRow>& raw) {
    const auto runRB = [&]() { return RBFunction{}(data, eraseOrder); };
    const auto runMap = [&]() { return MapFunction{}(data, eraseOrder); };

    if ((workloadIndex + eraseOrder) % 2 == 0) {
        (void)runRB();
        (void)runMap();
    } else {
        (void)runMap();
        (void)runRB();
    }

    for (int repetition = 1; repetition <= repetitions; ++repetition) {
        TimedSample rbSample;
        TimedSample mapSample;
        if ((repetition + workloadIndex + eraseOrder) % 2 == 0) {
            rbSample = runRB();
            mapSample = runMap();
        } else {
            mapSample = runMap();
            rbSample = runRB();
        }
        require(rbSample.checksum == mapSample.checksum,
                "RBTree and std::map operation checksums differ");
        raw.push_back({data.workload,
                       static_cast<int>(data.insertKeys.size()), operation,
                       eraseOrder, repetition, "RBTree", rbSample});
        raw.push_back({data.workload,
                       static_cast<int>(data.insertKeys.size()), operation,
                       eraseOrder, repetition, "std::map", mapSample});
    }
}

struct RBInsertRunner {
    TimedSample operator()(const Dataset& data, int) const {
        return timeRBInsert(data.insertKeys);
    }
};
struct MapInsertRunner {
    TimedSample operator()(const Dataset& data, int) const {
        return timeMapInsert(data.insertKeys);
    }
};
struct RBSearchRunner {
    TimedSample operator()(const Dataset& data, int) const {
        return timeRBSearch(data);
    }
};
struct MapSearchRunner {
    TimedSample operator()(const Dataset& data, int) const {
        return timeMapSearch(data);
    }
};
struct RBEraseRunner {
    TimedSample operator()(const Dataset& data, int order) const {
        return timeRBErase(data, static_cast<std::size_t>(order - 1));
    }
};
struct MapEraseRunner {
    TimedSample operator()(const Dataset& data, int order) const {
        return timeMapErase(data, static_cast<std::size_t>(order - 1));
    }
};

std::string compilerVersion() {
#if defined(__VERSION__)
    return __VERSION__;
#elif defined(_MSC_VER)
    return "MSVC " + std::to_string(_MSC_VER);
#else
    return "unknown";
#endif
}

void writeProtocol(const std::string& fileName, const std::string& mode,
                   const std::string& label, int repetitions,
                   const std::vector<int>& sizes) {
    std::ofstream out(fileName);
    if (!out) {
        throw std::runtime_error("cannot open " + fileName);
    }
    out << "parameter,value\n";
    out << "mode," << csvQuote(mode) << '\n';
    out << "compiler," << csvQuote(compilerVersion()) << '\n';
    out << "build_label," << csvQuote(label) << '\n';
    out << "cplusplus," << __cplusplus << '\n';
    out << "seed," << kSeed << '\n';
    out << "warmups," << kWarmups << '\n';
    out << "timed_repetitions," << repetitions << '\n';
    out << "sizes,";
    for (std::size_t i = 0; i < sizes.size(); ++i) {
        if (i != 0) out << ';';
        out << sizes[i];
    }
    out << '\n';
    out << "workloads,sorted;random;semi_sorted_10pct_swaps\n";
    out << "semi_sorted_rule,"
        << "shuffle floor(N*10/100) independently chosen position pairs\n";
    out << "deletion_orders,2 independent seeded shuffles of all present keys\n";
    out << "map_operations,emplace;find;erase(key)\n";
    out << "threading,single-thread CPU;GPU unused\n";
    out << "timer,std::chrono::steady_clock\n";
    out << "time_unit,nanoseconds per operation; medians from timed repetitions\n";
    out << "measurement_order,one warmup and alternating RBTree/map order\n";
    out << "search_checksum,observable volatile checksum outside timed region\n";
    out << "counter_pass,"
        << "structural counters are gathered separately from timed runs\n";
    out << "visited_nodes_definition,"
        << "RBTree key-search path nodes plus successor-walk nodes in erase\n";
    out << "map_comparator_definition,"
        << "calls to operator<; not exactly equivalent to RBTree node visits\n";
    out << "cpu_environment,not recorded; rerun on target machine for its results\n";
}

void writeBenchmarkCsvs(const std::string& prefix,
                        const std::string& label,
                        const std::string& mode, int repetitions,
                        const std::vector<int>& sizes,
                        const std::vector<RawRow>& raw,
                        const std::vector<StructureRow>& structures) {
    const std::string rawName = prefix + "_raw.csv";
    const std::string medianName = prefix + "_medians.csv";
    const std::string statsName = prefix + "_structure.csv";
    const std::string ratioName = prefix + "_ratios.csv";
    const std::string protocolName = prefix + "_protocol.csv";

    std::ofstream rawOut(rawName);
    std::ofstream medianOut(medianName);
    std::ofstream statsOut(statsName);
    std::ofstream ratioOut(ratioName);
    if (!rawOut || !medianOut || !statsOut || !ratioOut) {
        throw std::runtime_error("cannot create one or more benchmark CSVs");
    }

    rawOut << "workload,N,operation,deletion_order,repetition,structure,"
              "elapsed_ns,ns_per_operation,checksum\n";
    for (const RawRow& row : raw) {
        rawOut << csvQuote(row.workload) << ',' << row.n << ','
               << row.operation << ',' << row.eraseOrder << ','
               << row.repetition << ',' << row.structure << ','
               << row.sample.elapsedNs << ','
               << std::setprecision(12)
               << static_cast<double>(row.sample.elapsedNs) / row.n << ','
               << row.sample.checksum << '\n';
    }

    std::vector<MedianRow> medians;
    for (const RawRow& row : raw) {
        const bool seen = std::any_of(
            medians.begin(), medians.end(), [&](const MedianRow& existing) {
                return existing.workload == row.workload &&
                       existing.n == row.n &&
                       existing.operation == row.operation &&
                       existing.eraseOrder == row.eraseOrder &&
                       existing.structure == row.structure;
            });
        if (seen) continue;

        std::vector<double> elapsed;
        std::vector<double> perOperation;
        for (const RawRow& candidate : raw) {
            if (candidate.workload == row.workload && candidate.n == row.n &&
                candidate.operation == row.operation &&
                candidate.eraseOrder == row.eraseOrder &&
                candidate.structure == row.structure) {
                elapsed.push_back(static_cast<double>(
                    candidate.sample.elapsedNs));
                perOperation.push_back(static_cast<double>(
                    candidate.sample.elapsedNs) / row.n);
            }
        }
        medians.push_back({row.workload, row.n, row.operation,
                           row.eraseOrder, row.structure, median(elapsed),
                           median(perOperation)});
    }

    medianOut << "workload,N,operation,deletion_order,structure,repetitions,"
                 "median_elapsed_ns,median_ns_per_operation\n";
    for (const MedianRow& row : medians) {
        medianOut << csvQuote(row.workload) << ',' << row.n << ','
                  << row.operation << ',' << row.eraseOrder << ','
                  << row.structure << ',' << repetitions << ','
                  << std::setprecision(12) << row.medianElapsedNs << ','
                  << row.medianNsPerOperation << '\n';
    }

    statsOut << "workload,N,operation,deletion_order,structure,"
                "height_after_insert,total_rotations,rotations_per_operation,"
                "max_rotations_per_operation,total_recolorings,"
                "recolorings_per_operation,max_recolorings_per_operation,"
                "total_node_visits_or_comparator_calls,"
                "visits_or_comparisons_per_operation,"
                "max_visits_or_comparisons_per_operation\n";
    for (const StructureRow& row : structures) {
        statsOut << csvQuote(row.workload) << ',' << row.n << ','
                 << row.operation << ',' << row.eraseOrder << ','
                 << row.structure << ',' << row.height << ','
                 << row.rotations << ',' << std::setprecision(12)
                 << row.rotationsPerOperation << ',' << row.maxRotations
                 << ',' << row.recolorings << ','
                 << row.recoloringsPerOperation << ','
                 << row.maxRecolorings << ',' << row.visitedOrComparisons
                 << ',' << row.visitedOrComparisonsPerOperation << ','
                 << row.maxVisitedOrComparisons << '\n';
    }

    ratioOut << "workload,N,operation,deletion_order,"
                "map_to_rbtree_median_ns_ratio,rbtree_median_ns_per_operation,"
                "map_median_ns_per_operation\n";
    for (const MedianRow& rb : medians) {
        if (rb.structure != "RBTree") continue;
        const auto map = std::find_if(
            medians.begin(), medians.end(), [&](const MedianRow& row) {
                return row.workload == rb.workload && row.n == rb.n &&
                       row.operation == rb.operation &&
                       row.eraseOrder == rb.eraseOrder &&
                       row.structure == "std::map";
            });
        require(map != medians.end(), "missing std::map median");
        ratioOut << csvQuote(rb.workload) << ',' << rb.n << ','
                 << rb.operation << ',' << rb.eraseOrder << ','
                 << std::setprecision(12)
                 << (rb.medianNsPerOperation == 0
                         ? 0
                         : map->medianNsPerOperation /
                               rb.medianNsPerOperation)
                 << ',' << rb.medianNsPerOperation << ','
                 << map->medianNsPerOperation << '\n';
    }
    writeProtocol(protocolName, mode, label, repetitions, sizes);
    std::cout << "Wrote " << rawName << ", " << medianName << ", "
              << statsName << ", " << ratioName << ", " << protocolName
              << '\n';
}

void runBenchmark(bool quick, const std::string& prefix,
                  const std::string& label) {
    const std::vector<int> sizes = quick
        ? std::vector<int>{1000, 10000}
        : std::vector<int>(kFullSizes.begin(), kFullSizes.end());
    const int repetitions = quick ? 3 : 5;
    std::vector<RawRow> raw;
    std::vector<StructureRow> structures;

    for (std::size_t sizeIndex = 0; sizeIndex < sizes.size(); ++sizeIndex) {
        const int n = sizes[sizeIndex];
        for (int workload = 0; workload < 3; ++workload) {
            Dataset data = makeDataset(n, workload);
            std::cout << "Benchmark " << data.workload << ", N=" << n
                      << " ...\n";
            std::vector<StructureRow> stats = collectStructureStats(data);
            structures.insert(structures.end(), stats.begin(), stats.end());

            runTimedGroup<RBInsertRunner, MapInsertRunner>(
                data, "insert", 0, repetitions,
                static_cast<int>(workload), raw);
            runTimedGroup<RBSearchRunner, MapSearchRunner>(
                data, "find", 0, repetitions,
                static_cast<int>(workload), raw);
            for (int order = 1; order <= 2; ++order) {
                runTimedGroup<RBEraseRunner, MapEraseRunner>(
                    data, "erase", order, repetitions,
                    static_cast<int>(workload), raw);
            }
        }
    }
    writeBenchmarkCsvs(prefix, label, quick ? "quick" : "full",
                       repetitions, sizes, raw, structures);
}

struct SearchRawRow {
    int repetition = 0;
    int orderIndex = 0;
    std::string method;
    int n = 0;
    TimedSample sample;
};

TimedSample timeSearchMethod(RBTree& tree, std::map<int, int>& values,
                             const std::vector<int>& queries,
                             const std::string& method) {
    return timeOperations([&]() {
        std::uint64_t checksum = 0;
        for (int key : queries) {
            if (method == "RBTree_search") {
                const RBTree::Node* found = tree.findNode(key);
                if (found != nullptr) {
                    checksum += static_cast<std::uint64_t>(found->key) +
                                static_cast<std::uint64_t>(found->value) + 1;
                }
            } else if (method == "RBTree_lower_bound_style") {
                const RBTree::Node* found = tree.lowerBoundFind(key);
                if (found != nullptr) {
                    checksum += static_cast<std::uint64_t>(found->key) +
                                static_cast<std::uint64_t>(found->value) + 1;
                }
            } else {
                const auto found = values.find(key);
                if (found != values.end()) {
                    checksum += static_cast<std::uint64_t>(found->first) +
                                static_cast<std::uint64_t>(found->second) + 1;
                }
            }
        }
        return checksum;
    });
}

void runSearchExperiment(const std::string& prefix,
                         const std::string& label) {
    constexpr int n = 1000000;
    constexpr int repetitions = 9;
    Dataset data = makeDataset(n, 1);
    RBTree tree;
    populateTree(tree, data.insertKeys);
    validateOrThrow(tree, "search experiment RBTree");
    std::map<int, int> values;
    populateMap(values, data.insertKeys);
    const std::array<std::string, 3> methods{{
        "RBTree_search", "RBTree_lower_bound_style", "std_map_find"}};

    for (const std::string& method : methods) {
        const TimedSample sample =
            timeSearchMethod(tree, values, data.queries, method);
        require(sample.checksum ==
                    (static_cast<std::uint64_t>(n) * (n - 1) + n),
                "search experiment checksum mismatch");
    }

    std::vector<SearchRawRow> raw;
    for (int repetition = 1; repetition <= repetitions; ++repetition) {
        const int start = (repetition - 1) % static_cast<int>(methods.size());
        for (int offset = 0; offset < static_cast<int>(methods.size());
             ++offset) {
            const int index = (start + offset) %
                              static_cast<int>(methods.size());
            TimedSample sample = timeSearchMethod(
                tree, values, data.queries, methods[static_cast<std::size_t>(index)]);
            require(sample.checksum ==
                        (static_cast<std::uint64_t>(n) * (n - 1) + n),
                    "search experiment checksum mismatch");
            raw.push_back({repetition, offset, methods[static_cast<std::size_t>(index)],
                           n, sample});
        }
    }

    const std::string rawName = prefix + "_raw.csv";
    const std::string medianName = prefix + "_medians.csv";
    const std::string protocolName = prefix + "_protocol.csv";
    std::ofstream rawOut(rawName);
    std::ofstream medianOut(medianName);
    if (!rawOut || !medianOut) {
        throw std::runtime_error("cannot create search experiment CSVs");
    }
    rawOut << "build_label,repetition,measurement_order,method,N,elapsed_ns,"
              "ns_per_operation,checksum\n";
    for (const SearchRawRow& row : raw) {
        rawOut << csvQuote(label) << ',' << row.repetition << ','
               << row.orderIndex + 1 << ',' << row.method << ',' << row.n
               << ',' << row.sample.elapsedNs << ',' << std::setprecision(12)
               << static_cast<double>(row.sample.elapsedNs) / row.n << ','
               << row.sample.checksum << '\n';
    }
    medianOut << "build_label,method,N,repetitions,median_elapsed_ns,"
                 "median_ns_per_operation\n";
    for (const std::string& method : methods) {
        std::vector<double> elapsed;
        std::vector<double> perOperation;
        for (const SearchRawRow& row : raw) {
            if (row.method == method) {
                elapsed.push_back(static_cast<double>(row.sample.elapsedNs));
                perOperation.push_back(
                    static_cast<double>(row.sample.elapsedNs) / row.n);
            }
        }
        medianOut << csvQuote(label) << ',' << method << ',' << n << ','
                  << repetitions << ',' << std::setprecision(12)
                  << median(elapsed) << ',' << median(perOperation) << '\n';
    }
    writeProtocol(protocolName, "search_experiment", label, repetitions,
                  std::vector<int>{n});
    std::cout << "Wrote " << rawName << ", " << medianName << ", "
              << protocolName << '\n';
}

void testEdgeCases() {
    RBTree tree;
    std::string error;
    require(tree.size() == 0 && tree.validate(error),
            "empty tree validation failed");
    require(tree.findNode(10) == nullptr, "empty tree search should miss");
    require(!tree.erase(10), "erase from empty tree should fail");

    require(tree.emplace(10, 100), "single-root insertion failed");
    require(tree.findNode(10)->value == 100, "stored value mismatch");
    require(!tree.emplace(10, 999), "duplicate insertion should fail");
    require(tree.findNode(10)->value == 100,
            "duplicate emplace should preserve the original value");
    require(tree.erase(10), "single-root deletion failed");
    require(tree.size() == 0 && tree.validate(error),
            "single-root deletion did not restore empty tree");
    require(!tree.erase(10), "repeated erase should fail");

    const std::array<int, 11> keys{{10, 5, 15, 1, 7, 12, 20, 0, 2, 6, 8}};
    for (int key : keys) {
        require(tree.emplace(key, key), "edge-case insertion failed");
    }
    require(tree.validate(error), "edge-case setup invalid: " + error);
    const std::array<int, 11> deletionOrder{{10, 0, 20, 5, 15, 1,
                                             7, 12, 2, 6, 8}};
    for (int key : deletionOrder) {
        require(tree.erase(key), "edge-case deletion failed");
        require(tree.validate(error), "edge-case deletion invalid: " + error);
    }
    require(tree.size() == 0, "edge-case deletions left nodes");

    for (int i = 0; i < 256; ++i) {
        require(tree.emplace(i, -i), "ascending stress insertion failed");
    }
    for (int i = 255; i >= 0; --i) {
        require(tree.erase(i), "descending stress deletion failed");
    }
    require(tree.validate(error) && tree.size() == 0,
            "ascending/descending stress left an invalid tree");
}

void testExampleCounters() {
    InstrumentedRBTree tree;
    const std::array<int, 7> keys{{7, 58, 48, 12, 3, 22, 31}};
    for (int key : keys) {
        tree.beginOperation();
        tree.emplace(key, key);
    }
    const OperationStats totals = tree.totalStats();
    require(totals.rotations == 3, "example must produce exactly 3 rotations");
    require(totals.recolorings == 12,
            "example must produce exactly 12 effective recolorings");
    validateOrThrow(tree, "example insertion");
}

void testRandomDifferential() {
    RBTree tree;
    std::map<int, int> reference;
    std::mt19937 generator(0xC0FFEEu);
    std::uniform_int_distribution<int> keyDistribution(-500, 500);
    std::uniform_int_distribution<int> valueDistribution(
        std::numeric_limits<int>::min(), std::numeric_limits<int>::max());
    std::uniform_int_distribution<int> operationDistribution(0, 99);

    for (int step = 0; step < 30000; ++step) {
        const int key = keyDistribution(generator);
        const int choice = operationDistribution(generator);
        if (choice < 40) {
            const int value = valueDistribution(generator);
            const bool treeInserted = tree.emplace(key, value);
            const bool mapInserted = reference.emplace(key, value).second;
            require(treeInserted == mapInserted,
                    "random insertion result differs from std::map");
        } else if (choice < 70) {
            const bool treeErased = tree.erase(key);
            const bool mapErased = reference.erase(key) != 0;
            require(treeErased == mapErased,
                    "random erase result differs from std::map");
        } else {
            const RBTree::Node* treeFound = tree.findNode(key);
            const auto mapFound = reference.find(key);
            require((treeFound != nullptr) ==
                        (mapFound != reference.end()),
                    "random search presence differs from std::map");
            if (treeFound != nullptr) {
                require(treeFound->value == mapFound->second,
                        "random search value differs from std::map");
            }
        }

        require(tree.size() == reference.size(),
                "random-operation size differs from std::map");
        if (step % 97 == 0) {
            validateOrThrow(tree, "random differential test");
            for (const auto& entry : reference) {
                const RBTree::Node* found = tree.findNode(entry.first);
                require(found != nullptr && found->value == entry.second,
                        "full random differential check failed");
            }
        }
    }
    validateOrThrow(tree, "final random differential test");
    require(tree.size() == reference.size(),
            "final random differential size mismatch");
}

void runTests() {
    testEdgeCases();
    testExampleCounters();
    testRandomDifferential();
    std::cout << "All tests passed. Observable checksum="
              << gObservableChecksum << '\n';
}

struct Arguments {
    std::string mode;
    std::string prefix = "rbtree";
    std::string label = "unspecified";
};

Arguments parseArguments(int argc, char** argv) {
    Arguments args;
    for (int i = 1; i < argc; ++i) {
        const std::string argument(argv[i]);
        if (argument == "--test" || argument == "--quick" ||
            argument == "--full" || argument == "--search") {
            if (!args.mode.empty()) {
                throw std::runtime_error("choose exactly one execution mode");
            }
            args.mode = argument;
        } else if (argument == "--prefix" && i + 1 < argc) {
            args.prefix = argv[++i];
        } else if (argument == "--label" && i + 1 < argc) {
            args.label = argv[++i];
        } else {
            throw std::runtime_error("unknown or incomplete argument: " +
                                     argument);
        }
    }
    if (args.mode.empty()) {
        throw std::runtime_error(
            "usage: rbtree_benchmark.exe --test|--quick|--full|--search "
            "[--prefix NAME] [--label BUILD_LABEL]");
    }
    return args;
}

}  // namespace

int main(int argc, char** argv) {
    try {
        const Arguments args = parseArguments(argc, argv);
        if (args.mode == "--test") {
            runTests();
        } else if (args.mode == "--quick") {
            runBenchmark(true, args.prefix, args.label);
        } else if (args.mode == "--full") {
            runBenchmark(false, args.prefix, args.label);
        } else {
            runSearchExperiment(args.prefix, args.label);
        }
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "ERROR: " << error.what() << '\n';
        return 1;
    }
}
