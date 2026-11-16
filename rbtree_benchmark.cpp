#include <algorithm>
#include <chrono>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <random>
#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

namespace {

using Clock = std::chrono::steady_clock;
volatile std::uint64_t observableChecksum = 0;

class RBTree {
public:
    enum class Color { Red, Black };

    struct Node {
        int key;
        int value;
        Color color;
        Node* parent;
        Node* left;
        Node* right;
    };

    RBTree() {
        nil_.color = Color::Black;
        nil_.parent = nil_.left = nil_.right = &nil_;
        root_ = &nil_;
    }

    RBTree(const RBTree&) = delete;
    RBTree& operator=(const RBTree&) = delete;

    ~RBTree() {
        clear(root_);
    }

    bool insert(int key, int value) {
        Node* parent = &nil_;
        Node* current = root_;
        while (current != &nil_) {
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
        fixInsert(node);
        return true;
    }

    Node* find(int key) {
        Node* current = root_;
        while (current != &nil_) {
            if (key == current->key) {
                return current;
            }
            current = key < current->key ? current->left : current->right;
        }
        return nullptr;
    }

    bool erase(int key) {
        Node* target = root_;
        while (target != &nil_ && target->key != key) {
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
            moved->color = target->color;
        }

        delete target;
        --size_;
        if (originalColor == Color::Black) {
            fixErase(fixNode);
        }
        if (root_ != &nil_) {
            root_->parent = &nil_;
        }
        nil_.parent = &nil_;
        return true;
    }

    std::size_t size() const {
        return size_;
    }

    void display() const {
        if (root_ == &nil_) {
            std::cout << "(arbre vide)\n";
            return;
        }
        displayInOrder(root_);
    }

    bool validate(std::string& error) const {
        if (nil_.color != Color::Black || nil_.left != &nil_ ||
            nil_.right != &nil_) {
            error = "sentinelle NIL invalide";
            return false;
        }
        if (root_ == &nil_) {
            if (size_ != 0) {
                error = "taille incorrecte pour un arbre vide";
                return false;
            }
            return true;
        }
        if (root_->parent != &nil_ || root_->color != Color::Black) {
            error = "racine invalide";
            return false;
        }

        std::size_t count = 0;
        int blackHeight = 0;
        if (!validateNode(root_, &nil_,
                          std::numeric_limits<long long>::lowest(),
                          std::numeric_limits<long long>::max(), count,
                          blackHeight, error)) {
            return false;
        }
        if (count != size_) {
            error = "la taille stockee ne correspond pas au nombre de noeuds";
            return false;
        }
        return true;
    }

private:
    Node nil_{};
    Node* root_ = nullptr;
    std::size_t size_ = 0;

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
    }

    void fixInsert(Node* node) {
        while (node->parent->color == Color::Red) {
            if (node->parent == node->parent->parent->left) {
                Node* uncle = node->parent->parent->right;
                if (uncle->color == Color::Red) {
                    node->parent->color = Color::Black;
                    uncle->color = Color::Black;
                    node->parent->parent->color = Color::Red;
                    node = node->parent->parent;
                } else {
                    if (node == node->parent->right) {
                        node = node->parent;
                        rotateLeft(node);
                    }
                    node->parent->color = Color::Black;
                    node->parent->parent->color = Color::Red;
                    rotateRight(node->parent->parent);
                }
            } else {
                Node* uncle = node->parent->parent->left;
                if (uncle->color == Color::Red) {
                    node->parent->color = Color::Black;
                    uncle->color = Color::Black;
                    node->parent->parent->color = Color::Red;
                    node = node->parent->parent;
                } else {
                    if (node == node->parent->left) {
                        node = node->parent;
                        rotateRight(node);
                    }
                    node->parent->color = Color::Black;
                    node->parent->parent->color = Color::Red;
                    rotateLeft(node->parent->parent);
                }
            }
        }
        root_->color = Color::Black;
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

    Node* minimum(Node* node) const {
        while (node->left != &nil_) {
            node = node->left;
        }
        return node;
    }

    void fixErase(Node* node) {
        while (node != root_ && node->color == Color::Black) {
            if (node == node->parent->left) {
                Node* sibling = node->parent->right;
                if (sibling->color == Color::Red) {
                    sibling->color = Color::Black;
                    node->parent->color = Color::Red;
                    rotateLeft(node->parent);
                    sibling = node->parent->right;
                }
                if (sibling->left->color == Color::Black &&
                    sibling->right->color == Color::Black) {
                    if (sibling != &nil_) {
                        sibling->color = Color::Red;
                    }
                    node = node->parent;
                } else {
                    if (sibling->right->color == Color::Black) {
                        sibling->left->color = Color::Black;
                        sibling->color = Color::Red;
                        rotateRight(sibling);
                        sibling = node->parent->right;
                    }
                    sibling->color = node->parent->color;
                    node->parent->color = Color::Black;
                    sibling->right->color = Color::Black;
                    rotateLeft(node->parent);
                    node = root_;
                }
            } else {
                Node* sibling = node->parent->left;
                if (sibling->color == Color::Red) {
                    sibling->color = Color::Black;
                    node->parent->color = Color::Red;
                    rotateRight(node->parent);
                    sibling = node->parent->left;
                }
                if (sibling->right->color == Color::Black &&
                    sibling->left->color == Color::Black) {
                    if (sibling != &nil_) {
                        sibling->color = Color::Red;
                    }
                    node = node->parent;
                } else {
                    if (sibling->left->color == Color::Black) {
                        sibling->right->color = Color::Black;
                        sibling->color = Color::Red;
                        rotateLeft(sibling);
                        sibling = node->parent->left;
                    }
                    sibling->color = node->parent->color;
                    node->parent->color = Color::Black;
                    sibling->left->color = Color::Black;
                    rotateRight(node->parent);
                    node = root_;
                }
            }
        }
        node->color = Color::Black;
    }

    bool validateNode(const Node* node, const Node* expectedParent,
                      long long lower, long long upper, std::size_t& count,
                      int& blackHeight, std::string& error) const {
        if (node == &nil_) {
            blackHeight = 1;
            return true;
        }
        if (node->parent != expectedParent) {
            error = "pointeur parent incoherent";
            return false;
        }
        if (node->key <= lower || node->key >= upper) {
            error = "ordre des cles invalide";
            return false;
        }
        if (node->color == Color::Red &&
            (node->left->color == Color::Red ||
             node->right->color == Color::Red)) {
            error = "un noeud rouge a un enfant rouge";
            return false;
        }

        ++count;
        int leftHeight = 0;
        int rightHeight = 0;
        if (!validateNode(node->left, node, lower, node->key, count,
                          leftHeight, error) ||
            !validateNode(node->right, node, node->key, upper, count,
                          rightHeight, error)) {
            return false;
        }
        if (leftHeight != rightHeight) {
            error = "hauteurs noires differentes";
            return false;
        }
        blackHeight = leftHeight + (node->color == Color::Black ? 1 : 0);
        return true;
    }

    void displayInOrder(const Node* node) const {
        if (node == &nil_) {
            return;
        }
        displayInOrder(node->left);
        std::cout << node->key << " : " << node->value << " ("
                  << (node->color == Color::Red ? 'R' : 'B') << ")\n";
        displayInOrder(node->right);
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

void check(bool condition, const std::string& message) {
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

struct Sample {
    double nanosecondsPerOperation;
    std::uint64_t checksum;
};

template <typename Function>
Sample measure(Function&& operation, std::size_t count) {
    const auto start = Clock::now();
    const std::uint64_t checksum = operation();
    const auto finish = Clock::now();
    observableChecksum = observableChecksum ^ checksum;
    const double elapsed = static_cast<double>(
        std::chrono::duration_cast<std::chrono::nanoseconds>(
            finish - start).count());
    return {elapsed / static_cast<double>(count), checksum};
}

Sample measureTreeInsert(const std::vector<int>& keys) {
    RBTree tree;
    Sample sample = measure([&]() {
        std::uint64_t inserted = 0;
        for (int key : keys) {
            inserted += tree.insert(key, key);
        }
        return inserted;
    }, keys.size());
    validateOrThrow(tree, "apres insertion RBTree");
    check(tree.size() == keys.size(), "taille RBTree incorrecte apres insertion");
    return sample;
}

Sample measureMapInsert(const std::vector<int>& keys) {
    std::map<int, int> values;
    Sample sample = measure([&]() {
        std::uint64_t inserted = 0;
        for (int key : keys) {
            inserted += values.emplace(key, key).second;
        }
        return inserted;
    }, keys.size());
    check(values.size() == keys.size(), "taille std::map incorrecte");
    return sample;
}

Sample measureTreeFind(const std::vector<int>& keys,
                       const std::vector<int>& queries) {
    RBTree tree;
    for (int key : keys) {
        tree.insert(key, key);
    }
    validateOrThrow(tree, "avant recherche RBTree");
    return measure([&]() {
        std::uint64_t checksum = 0;
        for (int key : queries) {
            const RBTree::Node* found = tree.find(key);
            if (found != nullptr) {
                checksum += static_cast<std::uint64_t>(found->key) +
                            static_cast<std::uint64_t>(found->value) + 1;
            }
        }
        return checksum;
    }, queries.size());
}

Sample measureMapFind(const std::vector<int>& keys,
                      const std::vector<int>& queries) {
    std::map<int, int> values;
    for (int key : keys) {
        values.emplace(key, key);
    }
    return measure([&]() {
        std::uint64_t checksum = 0;
        for (int key : queries) {
            const auto found = values.find(key);
            if (found != values.end()) {
                checksum += static_cast<std::uint64_t>(found->first) +
                            static_cast<std::uint64_t>(found->second) + 1;
            }
        }
        return checksum;
    }, queries.size());
}

Sample measureTreeErase(const std::vector<int>& keys,
                        const std::vector<int>& eraseOrder) {
    RBTree tree;
    for (int key : keys) {
        tree.insert(key, key);
    }
    Sample sample = measure([&]() {
        std::uint64_t erased = 0;
        for (int key : eraseOrder) {
            erased += tree.erase(key);
        }
        return erased;
    }, eraseOrder.size());
    validateOrThrow(tree, "apres suppression RBTree");
    check(tree.size() == 0, "RBTree non vide apres suppression");
    return sample;
}

Sample measureMapErase(const std::vector<int>& keys,
                       const std::vector<int>& eraseOrder) {
    std::map<int, int> values;
    for (int key : keys) {
        values.emplace(key, key);
    }
    Sample sample = measure([&]() {
        std::uint64_t erased = 0;
        for (int key : eraseOrder) {
            erased += values.erase(key);
        }
        return erased;
    }, eraseOrder.size());
    check(values.empty(), "std::map non vide apres suppression");
    return sample;
}

template <typename TreeOperation, typename MapOperation>
void benchmarkOperation(const std::string& name, TreeOperation treeOperation,
                        MapOperation mapOperation, int repetitions) {
    const Sample warmTree = treeOperation();
    const Sample warmMap = mapOperation();
    check(warmTree.checksum == warmMap.checksum,
          "checksums differents pendant la chauffe");

    std::vector<double> treeTimes;
    std::vector<double> mapTimes;
    for (int repetition = 0; repetition < repetitions; ++repetition) {
        Sample treeSample{};
        Sample mapSample{};
        if (repetition % 2 == 0) {
            treeSample = treeOperation();
            mapSample = mapOperation();
        } else {
            mapSample = mapOperation();
            treeSample = treeOperation();
        }
        check(treeSample.checksum == mapSample.checksum,
              "checksums differents entre RBTree et std::map");
        treeTimes.push_back(treeSample.nanosecondsPerOperation);
        mapTimes.push_back(mapSample.nanosecondsPerOperation);
    }

    std::sort(treeTimes.begin(), treeTimes.end());
    std::sort(mapTimes.begin(), mapTimes.end());
    const double treeMedian = treeTimes[treeTimes.size() / 2];
    const double mapMedian = mapTimes[mapTimes.size() / 2];
    std::cout << std::left << std::setw(13) << name << std::right
              << std::setw(15) << std::fixed << std::setprecision(2)
              << treeMedian << std::setw(15) << mapMedian << std::setw(15)
              << (treeMedian == 0.0 ? 0.0 : mapMedian / treeMedian) << '\n';
}

void runBenchmark(int n) {
    std::mt19937 generator(0x5EED2026u);
    std::uniform_int_distribution<int> keyDistribution(0, 4 * n);
    std::unordered_set<int> uniqueKeys;
    uniqueKeys.reserve(static_cast<std::size_t>(n) * 2);
    std::vector<int> keys;
    keys.reserve(static_cast<std::size_t>(n));
    while (keys.size() < static_cast<std::size_t>(n)) {
        const int key = keyDistribution(generator);
        if (uniqueKeys.insert(key).second) {
            keys.push_back(key);
        }
    }
    std::shuffle(keys.begin(), keys.end(), generator);

    std::vector<int> queries = keys;
    std::shuffle(queries.begin(), queries.end(), generator);
    std::vector<int> eraseOrder = keys;
    std::shuffle(eraseOrder.begin(), eraseOrder.end(), generator);

    std::cout << "\nBenchmark aleatoire, N=" << n
              << " (5 repetitions, mediane, ns/operation)\n";
    std::cout << std::left << std::setw(13) << "Operation"
              << std::right << std::setw(15) << "RBTree"
              << std::setw(15) << "std::map"
              << std::setw(15) << "map/RBTree" << '\n';

    benchmarkOperation(
        "Insertion",
        [&]() { return measureTreeInsert(keys); },
        [&]() { return measureMapInsert(keys); }, 5);
    benchmarkOperation(
        "Recherche",
        [&]() { return measureTreeFind(keys, queries); },
        [&]() { return measureMapFind(keys, queries); }, 5);
    benchmarkOperation(
        "Suppression",
        [&]() { return measureTreeErase(keys, eraseOrder); },
        [&]() { return measureMapErase(keys, eraseOrder); }, 5);

    std::cout << "Checksum observable : " << observableChecksum << "\n\n";
}

void runTests() {
    RBTree tree;
    std::map<int, int> reference;
    std::string error;

    check(tree.validate(error), "arbre vide invalide");
    const std::vector<int> edgeKeys{10, 5, 15, 1, 7, 12, 20, 0, 2, 6, 8};
    for (int key : edgeKeys) {
        check(tree.insert(key, key), "insertion de test impossible");
        reference.emplace(key, key);
    }
    const std::vector<int> edgeDeletes{10, 0, 20, 5, 15, 1, 7, 12, 2, 6, 8};
    for (int key : edgeDeletes) {
        check(tree.erase(key) && reference.erase(key) == 1,
              "suppression limite incorrecte");
        validateOrThrow(tree, "test de suppression limite");
    }
    check(tree.size() == 0, "arbre non vide apres le test limite");
    check(!tree.erase(10), "suppression absente devrait echouer");

    std::mt19937 generator(0xC0FFEEu);
    std::uniform_int_distribution<int> keyDistribution(-500, 500);
    std::uniform_int_distribution<int> valueDistribution(-100000, 100000);
    std::uniform_int_distribution<int> operationDistribution(0, 99);
    for (int step = 0; step < 20000; ++step) {
        const int key = keyDistribution(generator);
        const int operation = operationDistribution(generator);
        if (operation < 40) {
            const int value = valueDistribution(generator);
            check(tree.insert(key, value) == reference.emplace(key, value).second,
                  "insertion aleatoire differente de std::map");
        } else if (operation < 70) {
            check(tree.erase(key) == (reference.erase(key) != 0),
                  "suppression aleatoire differente de std::map");
        } else {
            const RBTree::Node* found = tree.find(key);
            const auto expected = reference.find(key);
            check((found != nullptr) == (expected != reference.end()),
                  "recherche aleatoire differente de std::map");
            if (found != nullptr) {
                check(found->value == expected->second,
                      "valeur trouvee differente de std::map");
            }
        }
        check(tree.size() == reference.size(),
              "tailles differentes dans le test aleatoire");
        if (step % 101 == 0) {
            validateOrThrow(tree, "test aleatoire");
        }
    }
    validateOrThrow(tree, "fin du test aleatoire");
    std::cout << "Tous les tests sont passes.\n";
}

int readInteger(const std::string& prompt) {
    int value = 0;
    while (true) {
        std::cout << prompt;
        if (std::cin >> value) {
            return value;
        }
        if (std::cin.eof()) {
            throw std::runtime_error("fin de l'entree utilisateur");
        }
        std::cin.clear();
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        std::cout << "Entree invalide, recommencez.\n";
    }
}

void showMenu() {
    std::cout << "1. Inserer une paire cle/valeur\n"
              << "2. Rechercher une cle\n"
              << "3. Supprimer une cle\n"
              << "4. Afficher les noeuds (ordre croissant)\n"
              << "5. Valider les invariants\n"
              << "6. Benchmark aleatoire contre std::map\n"
              << "7. Lancer les tests automatiques\n"
              << "0. Quitter\n";
}

void runMenu() {
    RBTree tree;
    bool running = true;
    while (running) {
        showMenu();
        const int choice = readInteger("Choix : ");
        switch (choice) {
        case 1: {
            const int key = readInteger("Cle : ");
            const int value = readInteger("Valeur : ");
            std::cout << (tree.insert(key, value)
                              ? "Paire inseree.\n"
                              : "Cle deja presente; valeur inchangee.\n");
            break;
        }
        case 2: {
            const int key = readInteger("Cle a rechercher : ");
            const RBTree::Node* found = tree.find(key);
            if (found == nullptr) {
                std::cout << "Cle absente.\n";
            } else {
                std::cout << "Trouvee : " << found->key << " -> "
                          << found->value << '\n';
            }
            break;
        }
        case 3: {
            const int key = readInteger("Cle a supprimer : ");
            std::cout << (tree.erase(key) ? "Cle supprimee.\n"
                                         : "Cle absente.\n");
            break;
        }
        case 4:
            tree.display();
            break;
        case 5: {
            std::string error;
            if (tree.validate(error)) {
                std::cout << "Invariants valides; taille = " << tree.size()
                          << ".\n";
            } else {
                std::cout << "ERREUR : " << error << '\n';
            }
            break;
        }
        case 6: {
            const int n = readInteger("Nombre de cles N (1 a 2000000) : ");
            if (n < 1 || n > 2000000) {
                std::cout << "N doit etre compris entre 1 et 2000000.\n";
            } else {
                runBenchmark(n);
            }
            break;
        }
        case 7:
            runTests();
            break;
        case 0:
            running = false;
            break;
        default:
            std::cout << "Choix inconnu.\n";
            break;
        }
        std::cout << '\n';
    }
}

}  // namespace

int main(int argc, char** argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--test") {
            runTests();
            return 0;
        }
        if (argc != 1) {
            std::cerr << "Usage : rbtree_benchmark.exe [--test]\n";
            return 1;
        }
        runMenu();
        return 0;
    } catch (const std::exception& error) {
        std::cerr << "Erreur : " << error.what() << '\n';
        return 1;
    }
}
