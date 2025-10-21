/**
 * \file logic_parser.cpp
 * \brief Implements functions for parsing, converting, and evaluating propositional logic formulas.
 *
 * This file contains definitions for a Node structure to represent a parse tree,
 * along with functions for infix-to-prefix conversion, parse tree construction, 
 * formula evaluation, and Conjunctive Normal Form (CNF) conversion/analysis.
 */

#include <bits/stdc++.h> /**< \brief Includes all standard C++ libraries (e.g., iostream, vector, string, stack, map, set). */
using namespace std; /**< \brief Brings all identifiers from the std namespace into the global scope. */

// ---------------- STRUCT ----------------

/**
 * \struct Node
 * \brief Represents a node in the expression parse tree.
 *
 * Stores the value (operator or atom) and pointers to its left and right children.
 */
struct Node {
    /** \var value 
     * \brief The operator (~, *, +, >) or a propositional atom (e.g., 'p', 'x1'). 
     */
    string value;
    /** \var left 
     * \brief Pointer to the left child node. 
     */
    Node* left;
    /** \var right 
     * \brief Pointer to the right child node. 
     */
    Node* right;

    /**
     * \brief Constructor for a leaf node (atom).
     * \param val The atom's string value.
     */
    Node(string val) {
        value = val;
        left = nullptr;
        right = nullptr;
    }

    /**
     * \brief Constructor for an internal node (operator).
     * \param val The operator's string value.
     * \param l Pointer to the left child.
     * \param r Pointer to the right child.
     */
    Node(string val, Node* l, Node* r) { 
        value = val;
        left = l;
        right = r;
    }
};

// ---------------- HELPER FUNCTIONS ----------------

/**
 * \brief Checks if a given string token is a supported logical operator.
 *
 * Supported operators: ~ (NOT), * (AND), + (OR), > (IMPLIES).
 * \param s The string token to check.
 * \return true if the token is an operator, false otherwise.
 */
bool isOperator(const string &s) {
    return (s == "*" || s == "+" || s == ">" || s == "~");
}

/**
 * \brief Returns the precedence level for a logical operator.
 *
 * Precedence order (highest to lowest):
 * 3: ~ (NOT)
 * 2: * (AND)
 * 1: + (OR)
 * 0: > (IMPLIES)
 * \param op The operator string.
 * \return An integer representing the precedence level, or -1 if not an operator.
 */
int precedence(const string &op) {
    if (op == "~") return 3;
    if (op == "*") return 2;
    if (op == "+") return 1;
    if (op == ">") return 0;
    return -1;
}

// ---------------- INFIX → PREFIX ----------------

/**
 * \brief Tokenizes an infix logical expression string into a vector of strings.
 *
 * Handles single-character operators, propositional atoms, and skips whitespace.
 * \param expr The input infix expression string.
 * \return A vector of strings representing the tokens.
 */
vector<string> tokenize(const string &expr) {
    vector<string> tokens;
    string token;
    for (int i = 0; i < expr.size();) {
        if (isspace(expr[i])) { i++; continue; }
        if (isalnum(expr[i])) {
            token = "";
            while (i < expr.size() && (isalnum(expr[i]) || expr[i] == '_'))
                token += expr[i++];
            tokens.push_back(token);
        } else {
            // Removed: if (expr.substr(i, 3) == "<->") { ... }
            if (expr.substr(i, 1) == ">") {
                tokens.push_back(">");
                i += 1;
            } else {
                tokens.push_back(string(1, expr[i]));
                i++;
            }
        }
    }
    return tokens;
}

/**
 * \brief Converts an infix expression string to a vector of prefix tokens (Polish notation).
 *
 * This is achieved by reversing the infix expression, applying a modified Shunting-yard algorithm 
 * (as if converting to postfix), and then reversing the result.
 * \param expr The input infix expression string.
 * \return A vector of strings in prefix order.
 */
vector<string> infixToPrefix(const string &expr) {
    vector<string> tokens = tokenize(expr);
    reverse(tokens.begin(), tokens.end());

    // Swap parentheses for reverse-to-prefix conversion
    for (auto &t : tokens) {
        if (t == "(") t = ")";
        else if (t == ")") t = "(";
    }

    stack<string> ops;
    vector<string> output;

    for (string token : tokens) {
        if (isalnum(token[0]))
            output.push_back(token);
        else if (token == "(")
            ops.push(token);
        else if (token == ")") {
            while (!ops.empty() && ops.top() != "(") {
                output.push_back(ops.top());
                ops.pop();
            }
            if (!ops.empty()) ops.pop(); // Pop '('
        } else if (isOperator(token)) {
            // Right-associativity rule is implicitly handled by reversing and using '>'
            while (!ops.empty() && precedence(ops.top()) > precedence(token)) {
                output.push_back(ops.top());
                ops.pop();
            }
            ops.push(token);
        }
    }

    while (!ops.empty()) {
        output.push_back(ops.top());
        ops.pop();
    }

    reverse(output.begin(), output.end());
    return output;
}

// ---------------- PREFIX → PARSE TREE ----------------

/**
 * \brief Builds a parse tree from a vector of prefix tokens.
 *
 * Iterates through the prefix tokens in reverse order, using a stack to assemble the tree structure.
 * \param prefix A reference to the vector of strings in prefix order.
 * \return A pointer to the root Node of the constructed parse tree.
 */
Node* buildParseTree(vector<string> &prefix) {
    stack<Node*> st;
    for (int i = prefix.size() - 1; i >= 0; --i) {
        string token = prefix[i];
        if (isOperator(token)) {
            Node* node = new Node(token);
            if (token == "~") {
                // Unary operator: takes one operand from the stack (left child)
                if (st.empty()) return nullptr; // Error handling
                node->left = st.top(); st.pop();
            } else {
                // Binary operator: takes two operands from the stack (left and right children)
                if (st.size() < 2) return nullptr; // Error handling
                node->left = st.top(); st.pop();
                node->right = st.top(); st.pop();
            }
            st.push(node);
        } else {
            // Atom: create a new leaf node
            st.push(new Node(token));
        }
    }
    if (st.size() != 1) return nullptr; // Check for valid expression
    return st.top();
}

// ---------------- TREE → INFIX ----------------

/**
 * \brief Converts the expression parse tree back to a fully parenthesized infix string (in-order traversal).
 *
 * Uses parentheses for all sub-expressions to ensure correct order of operations.
 * \param root Pointer to the root Node of the parse tree.
 * \return The fully parenthesized infix expression string.
 */
string toInfix(Node* root) {
    if (!root) return "";
    if (!root->left && !root->right) return root->value; // Atom (leaf)
    
    if (root->value == "~") 
        return "(~" + toInfix(root->left) + ")"; // Unary operator (~A)
    
    // Binary operator ((A op B))
    return "(" + toInfix(root->left) + " " + root->value + " " + toInfix(root->right) + ")";
}

// ---------------- HEIGHT ----------------

/**
 * \brief Computes the height of the expression parse tree.
 *
 * The height is the length of the longest path from the root to a leaf node. An empty tree has height 0.
 * \param root Pointer to the root Node of the parse tree.
 * \return The integer height of the tree.
 */
int treeHeight(Node* root) {
    if (!root) return 0;
    return 1 + max(treeHeight(root->left), treeHeight(root->right));
}

// ---------------- EVALUATION ----------------

/**
 * \brief Recursively evaluates the truth value of the formula represented by the parse tree 
 * based on a given truth assignment for its atoms.
 * \param root Pointer to the root Node of the parse tree.
 * \param values A map of propositional atom names to their boolean truth values.
 * \return The boolean result of the formula evaluation.
 */
bool evaluate(Node* root, unordered_map<string, bool> &values) {
    if (!root->left && !root->right)
        return values.at(root->value); // Atom evaluation

    if (root->value == "~")
        return !evaluate(root->left, values);
    if (root->value == "*") // AND
        return evaluate(root->left, values) && evaluate(root->right, values);
    if (root->value == "+") // OR
        return evaluate(root->left, values) || evaluate(root->right, values);
    if (root->value == ">") // IMPLIES (A > B is ~A + B)
        return !evaluate(root->left, values) || evaluate(root->right, values);
    // Removed: Biconditional logic block
    
    return false; // Should only happen if the operator is unrecognized/removed
}

// ---------------- DIMACS (CNF) to STRING ----------------

/**
 * \brief Converts a formula in DIMACS CNF file format to a standard infix string representation.
 *
 * Clauses are represented as disjunctions (+, OR) and clauses are connected by conjunctions (*, AND).
 * \param filename The path to the DIMACS CNF file.
 * \return The formula as an infix string, or an empty string if the file fails to open.
 */
string dimacsToFormula(const string& filename) {
    ifstream file(filename);
    if (!file.is_open()) {
        cerr << "Error opening file\n";
        return "";
    }

    string line;
    stringstream formula;

    while (getline(file, line)) {
        if (line.empty() || line[0] == 'c' || line[0] == 'p') continue; // skip comments and header

        stringstream ss(line);
        int lit;
        formula << "(";
        bool first = true;
        while (ss >> lit && lit != 0) {
            if (!first) formula << " + "; // OR is '+'
            first = false;
            if (lit < 0)
                formula << "~x" << -lit;
            else
                formula << "x" << lit;
        }
        formula << ") * "; // AND is '*'
    }

    string output = formula.str();
    if (output.size() >= 3) output.erase(output.size() - 3); // remove last " * "
    cout << "Successfully converted the DIMACS file to formula string." << endl;
    return output;
}

// ---------------- TRUTH TABLE GENERATION ----------------

/**
 * \brief Traverses the parse tree to collect all unique propositional atoms.
 *
 * \param root Pointer to the root Node of the parse tree.
 * \param atoms A set of strings to store the collected atoms (ensures uniqueness and provides sorted order).
 */
void collectAtoms(Node* root, set<string>& atoms) {
    if (!root) return;
    if (!root->left && !root->right && !isOperator(root->value)) {
        atoms.insert(root->value);
    }
    collectAtoms(root->left, atoms);
    collectAtoms(root->right, atoms);
}

/**
 * \brief Evaluates a node given a complete truth assignment.
 *
 * This is a helper for the truth table generation.
 * \param root Pointer to the Node to evaluate.
 * \param values A constant map of propositional atom names to their boolean truth values.
 * \return The boolean result of the formula at that node.
 */
bool evaluateNode(Node* root, const unordered_map<string,bool>& values) {
    // This function is essentially a duplication of evaluate but is used internally for the table
    if (!root->left && !root->right) return values.at(root->value); 
    if (root->value == "~") return !evaluateNode(root->left, values);
    if (root->value == "*") return evaluateNode(root->left, values) && evaluateNode(root->right, values);
    if (root->value == "+") return evaluateNode(root->left, values) || evaluateNode(root->right, values);
    if (root->value == ">") return !evaluateNode(root->left, values) || evaluateNode(root->right, values);
    // Removed: Biconditional logic block
    return false; // Should not happen in a well-formed tree
}

/**
 * \brief Generates and prints the full truth table for the formula represented by the parse tree.
 *
 * Iterates through all $2^n$ possible truth assignments, where $n$ is the number of unique atoms.
 * \param root Pointer to the root Node of the parse tree.
 */
void generateTruthTable(Node* root) {
    if (!root) {
        cout << "Parse tree is empty!\n";
        return;
    }

    set<string> atomsSet;
    collectAtoms(root, atomsSet); 
    vector<string> atoms(atomsSet.begin(), atomsSet.end());
    int n = atoms.size();

    if (n == 0) {
        cout << "No propositional atoms found.\n";
        return;
    }

    // Header
    cout << "\n--- Truth Table ---\n";
    for (const auto& atom : atoms) cout << setw(6) << atom;
    cout << setw(10) << "Result\n";
    cout << string(6*n + 10, '-') << "\n";

    int total = 1 << n; // 2^n combinations
    for (int i = 0; i < total; ++i) {
        unordered_map<string,bool> assignment;
        for (int j = 0; j < n; ++j) {
            // Determine the truth value for the j-th atom in the i-th combination
            bool val = (i >> (n - j - 1)) & 1;
            assignment[atoms[j]] = val;
            cout << setw(6) << val;
        }
        bool result = evaluateNode(root, assignment);
        cout << setw(10) << result << "\n";
    }
}


/* ---------------- TASK 6 - CNF Conversion ---------------- */

/**
 * \brief Recursively eliminates implication (>) operators in the parse tree.
 *
 * Applies the transformations: A > B is replaced by ~A + B.
 * \param root Pointer to the current Node in the parse tree.
 * \return Pointer to the root of the modified subtree.
 */
Node* eliminateImplications(Node* root) {
    if (!root || (!root->left && !root->right)) return root;

    root->left = eliminateImplications(root->left);
    root->right = eliminateImplications(root->right);

    if (root->value == ">") {
        root->value = "+"; // A > B becomes ... + B
        Node* notLeft = new Node("~"); // new ~
        notLeft->left = root->left; // new ~A
        root->left = notLeft; // (~A) + B
    }
    // Removed: Biconditional note
    return root;
}

/**
 * \brief Recursively moves negations inward in the parse tree using De Morgan's laws and Double Negation.
 *
 * Applies: ~~A -> A; ~(A + B) -> ~A * ~B; ~(A * B) -> ~A + ~B.
 * \param root Pointer to the current Node in the parse tree.
 * \return Pointer to the root of the modified subtree (Negation Normal Form - NNF).
 */
Node* moveNegations(Node* root) {
    if (!root || (!root->left && !root->right)) return root;

    if (root->value == "~") {
        Node* child = root->left;
        if (!child) return nullptr; // Should not happen

        if (child->value == "~") {
            // Double Negation: ~~A -> A
            return moveNegations(child->left);
        }
        else if (child->value == "+") {
            // De Morgan's: ~(A + B) -> ~A * ~B
            Node* newNode = new Node("*");
            newNode->left = moveNegations(new Node("~", child->left, nullptr));
            newNode->right = moveNegations(new Node("~", child->right, nullptr));
            return newNode;
        }
        else if (child->value == "*") {
            // De Morgan's: ~(A * B) -> ~A + ~B
            Node* newNode = new Node("+");
            newNode->left = moveNegations(new Node("~", child->left, nullptr));
            newNode->right = moveNegations(new Node("~", child->right, nullptr));
            return newNode;
        }
        else {
            // Negation on an atom or literal, stop
            return root;
        }
    }

    // Apply recursively to children
    root->left = moveNegations(root->left);
    root->right = moveNegations(root->right);
    return root;
}

/**
 * \brief Recursively distributes OR over AND to complete the CNF conversion (Distributive Law).
 *
 * Applies: A + (B * C) -> (A + B) * (A + C).
 * \param root Pointer to the current Node in the parse tree (expected to be in NNF).
 * \return Pointer to the root of the final CNF subtree.
 */
Node* distributeOrOverAnd(Node* root) {
    if (!root || (!root->left && !root->right)) return root;

    root->left = distributeOrOverAnd(root->left);
    root->right = distributeOrOverAnd(root->right);

    if (root->value == "+") {
        Node* A = root->left;
        Node* B = root->right;

        // Case 1: (A * B) + C -> (A + C) * (B + C)
        if (A->value == "*") {
            Node* newNode = new Node("*");
            newNode->left = distributeOrOverAnd(new Node("+", A->left, B));
            newNode->right = distributeOrOverAnd(new Node("+", A->right, B));
            return newNode;
        }
        // Case 2: A + (B * C) -> (A + B) * (A + C)
        else if (B->value == "*") {
            Node* newNode = new Node("*");
            newNode->left = distributeOrOverAnd(new Node("+", A, B->left));
            newNode->right = distributeOrOverAnd(new Node("+", A, B->right));
            return newNode;
        }
    }
    return root;
}

/**
 * \brief Converts a propositional logic formula's parse tree into Conjunctive Normal Form (CNF).
 *
 * The conversion process involves three main steps:
 * 1. Eliminate all implications.
 * 2. Move negations inward to form Negation Normal Form (NNF).
 * 3. Distribute OR over AND.
 * \param root Pointer to the root Node of the original parse tree.
 * \return Pointer to the root Node of the resulting CNF parse tree.
 */
Node* convertToCNF(Node* root) {
    root = eliminateImplications(root);
    root = moveNegations(root);
    root = distributeOrOverAnd(root);
    return root;
}

/* ---------------- END CNF Conversion ---------------- */

/* ---------------- TASK 7 - CNF Validity Check ---------------- */

/**
 * \brief Recursively extracts literals from a clause (an OR-connected subtree).
 *
 * A clause is a disjunction of literals. Literals are atoms or negated atoms.
 * \param node Pointer to the current Node (should be the root of an OR-chain).
 * \param literals A vector of strings to store the extracted literals (e.g., "p", "~q").
 */
void getLiterals(Node* node, vector<string>& literals) {
    if (!node) return;

    if (node->value == "+") {
        // Recurse down the OR-chain
        getLiterals(node->left, literals);
        getLiterals(node->right, literals);
    } else if (node->value == "~") {
        // Negation: forms a negated literal (~atom)
        literals.push_back("~" + node->left->value);
    } else {
        // Atom: forms a positive literal
        literals.push_back(node->value);
    }
}

/**
 * \brief Collects all clauses from a CNF parse tree.
 *
 * Clauses are separated by the AND (*) operator. The root of the CNF tree is expected to be an AND-chain.
 * \param cnfRoot Pointer to the root of the CNF parse tree (expected to be an AND-chain).
 * \param clauses A vector of vector of strings to store the resulting clauses (each inner vector is a clause/disjunction).
 */
void collectClauses(Node* cnfRoot, vector<vector<string>>& clauses) {
    if (!cnfRoot) return;

    if (cnfRoot->value == "*") {
        // Recurse down the AND-chain
        collectClauses(cnfRoot->left, clauses);
        collectClauses(cnfRoot->right, clauses);
    } else {
        // Found a clause (which is an OR-chain or a single literal)
        vector<string> currentClause;
        getLiterals(cnfRoot, currentClause);
        clauses.push_back(currentClause);
    }
}

/**
 * \brief Analyzes the validity (tautology status) of each clause in a CNF formula.
 *
 * A clause is a tautology if it contains a literal and its negation (e.g., $A + \neg A$).
 * The overall CNF formula is only a tautology if every single clause is a tautology.
 * \param clauses The vector of clauses (from \ref collectClauses).
 * \param valid_count Reference to an integer to store the count of tautological clauses.
 * \param invalid_count Reference to an integer to store the count of non-tautological clauses.
 * \return true if the entire CNF formula is a tautology (all clauses are tautological), false otherwise.
 */
bool analyzeCNFValidity(const vector<vector<string>>& clauses, int& valid_count, int& invalid_count) {
    valid_count = 0;
    invalid_count = 0;

    if (clauses.empty()) {
        return true; 
    }

    for (const auto& clause : clauses) {
        set<string> literalsInClause;
        bool clauseIsTautology = false;

        for (const auto& literal : clause) {
            string negation;
            // Determine the negation of the current literal
            if (literal[0] == '~') {
                negation = literal.substr(1); // Literal is ~A, negation is A
            } else {
                negation = "~" + literal; // Literal is A, negation is ~A
            }

            // Check if the negation is already in the clause
            if (literalsInClause.count(negation)) {
                clauseIsTautology = true;
                break; 
            }
            literalsInClause.insert(literal);
        }

        if (clauseIsTautology) {
            valid_count++;
        } else {
            invalid_count++;
        }
    }

    return (invalid_count == 0);
}


// ---------------- MAIN ----------------

/**
 * \brief Main function to handle user interaction, execute formula processing tasks, and output results.
 *
 * Tasks include: Infix to Prefix conversion, Parse Tree construction, Infix output, 
 * Tree Height calculation, Manual Evaluation, Truth Table Generation, CNF Conversion, 
 * and CNF Validity Check. It can load an expression from user input or a DIMACS file.
 * \return 0 upon successful execution, 1 on error.
 */
int main() {
    cout << "Enter the infix logical expression (or leave blank to use CNF file): ";
    string infix_expr;
    getline(cin, infix_expr);

    // --- Case 1: User entered a formula manually ---
    if (!infix_expr.empty()) {
        cout << "\n--- Using User-Entered Expression ---" << endl;
        cout << "Expression: " << infix_expr << endl;
    } 
    // --- Case 2: No expression entered — load CNF file ---
    else {
        cout << "\nNo custom expression entered. Reading from CNF file..." << endl;
        string formula = dimacsToFormula("unif-c500-v250-s453695930.cnf");
        if (formula.empty()) {
            cerr << "Error: CNF file could not be loaded. Exiting.\n";
            return 1;
        }
        infix_expr = formula;
        cout << "\n--- DIMACS Conversion ---" << endl;
        cout << "Formula from CNF: " << formula << endl;
    }

    // --- Task 1: Infix → Prefix ---
    vector<string> prefix_tokens = infixToPrefix(infix_expr);
    string prefix_expr;
    for (const string& token : prefix_tokens) prefix_expr += token + " ";

    cout << "\n--- Task 1: Prefix Conversion ---" << endl;
    cout << "Infix: " << infix_expr << endl;
    cout << "Prefix: " << prefix_expr << endl;

    // --- Task 2: Prefix → Parse Tree ---
    Node* root = buildParseTree(prefix_tokens); 

    cout << "\n--- Task 2: Parse Tree Building ---" << endl;
    if (!root) {
        cout << "Tree could not be built! Check the input expression." << endl;
        return 1;
    }
    cout << "Parse Tree built successfully!" << endl;

    // --- Task 3: Tree → Infix ---
    string inOrder = toInfix(root);
    cout << "\n--- Task 3: Tree to Infix Conversion ---" << endl;
    cout << "In-order (Infix form): " << inOrder << endl;

    // --- Task 4: Tree Height ---
    int height = treeHeight(root);
    cout << "\n--- Task 4: Tree Height ---" << endl;
    cout << "Tree Height: " << height << endl;

    // --- Task 5: Evaluation ---
    cout << "\n--- Task 5: Formula Evaluation ---" << endl;
    unordered_map<string, bool> assignment;
    
    while (true) {
        string atom;
        cout << "Enter atom name (e.g., x1, p, y22) or STOP to end: ";
        cin >> atom;
        if (atom == "STOP") break;

        int val_input;
        cout << "Enter truth value for " << atom << " (0 for FALSE, 1 for TRUE): ";
        cin >> val_input;

        if (cin.fail() || (val_input != 0 && val_input != 1)) {
            cerr << "Invalid input. Please enter 0 or 1." << endl;
            cin.clear();
            cin.ignore(numeric_limits<streamsize>::max(), '\n');
            continue;
        }

        assignment[atom] = (val_input == 1);
    }

    if (!assignment.empty()) {
        bool result = evaluate(root, assignment); 
        cout << "\nEvaluation Result:" << endl;
        cout << "The formula evaluates to " << (result ? "TRUE" : "FALSE") << "." << endl;
    } else {
        cout << "No variables assigned. Skipping evaluation." << endl;
    }

    // ---- Generate Truth Table ---
    cout << "\n---Truth Table Generation ---" << endl;
    cout << "Do you want to generate a full truth table for this formula? (y/n): ";
    char choice;
    cin >> choice;
    if (choice == 'y' || choice == 'Y') {
        generateTruthTable(root);
    }

    // --- Task 6 & 7: CNF Conversion + Validity ---
    cout << "\n--- Task 6 & 7: CNF Conversion and Clause Validity ---" << endl;
    Node* cnfRoot = convertToCNF(root);
    string cnfInfix = toInfix(cnfRoot);
    cout << "\nCNF Form of Formula: " << cnfInfix << endl;

    vector<vector<string>> clauses;
    collectClauses(cnfRoot, clauses);

    int valid_count = 0, invalid_count = 0;
    bool all_valid = analyzeCNFValidity(clauses, valid_count, invalid_count);

    cout << "\nCNF Clause Validity Analysis:" << endl;
    cout << "Valid (tautological) clauses: " << valid_count << endl;
    cout << "Non-tautological clauses: " << invalid_count << endl;

    if (all_valid)
        cout << "The CNF is valid (all clauses are tautologies)." << endl;
    else
        cout << "The CNF is not valid (some clauses are not tautologies)." << endl;
    
    // NOTE: Memory cleanup (e.g., deleteTree) is typically needed here.

    return 0;
}