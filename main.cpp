#include <iostream>
#include <type_traits>
#include <vector>
#include <memory>
#include <map>
#include <set>
#include <cassert>
#include <algorithm>
#define INIT_COST 0
#define MAX_COST 99999

enum Opcode {
    None,
    Add,
    Sub,
    Assign,
    Const,
    Reg,
};

std::string getOpName(Opcode op) {
    switch (op) {
        case None:
            return "";
        case Add:
            return "+";
        case Sub:
            return "-";
        case Assign:
            return "=";
        case Const:
            return "Int";
        case Reg:
            return "Reg";
    }
}

int getOpArity(Opcode op) {
    switch (op) {
        case None:
            return 0;
        case Add:
            return 2;
        case Sub:
            return 2;
        case Assign:
            return 2;
        case Const:
            return 0;
    }
}

class Rule;
struct Symbol {
    Opcode opcode = None;
    std::string name;
    bool isNT = false;
    std::set<Rule *> rules;

    Symbol(Opcode opcode) : opcode(opcode), isNT(false) {}

    Symbol(const std::string &name) : name(name), isNT(true) {}

    bool isTerminal() {
        return !isNT;
    }

    bool isNonterminal() {
        return isNT;
    }

    void dump(std::ostream &os) {
        os << (opcode == None ? name : getOpName(opcode));
    }

};

struct Rule {
    // A = op(X, Y, Z)
    // A = X
    Symbol *lhs = nullptr;
    Opcode op = None;
    std::vector<Symbol *> rhs;
    int cost = INIT_COST;

    Rule(Symbol *lhs, const std::vector<Symbol *> &rhs, int cost = INIT_COST) : lhs(lhs), rhs(rhs), cost(cost) {
        lhs->rules.insert(this);
    }

    Rule(Symbol *lhs, Opcode op, const std::vector<Symbol *> &rhs, int cost = INIT_COST) : lhs(lhs), op(op), rhs(rhs),
                                                                                      cost(cost) {
        lhs->rules.insert(this);
    }

    bool isArityZero() const {
        return op == None;
    }

    Symbol *getArityZeroRHS() const {
        if (op != None) {
            return nullptr;
        }
        return rhs.front();
    }

    int getArity() const {
        return rhs.size();
    }

    Symbol *getNonterminal() const {
        return lhs;
    }

    void dump(std::ostream &os) {
        lhs->dump(os);
        os << " -> ";
        bool close = false;
        switch (op) {
            case None:
                break;
            case Add:
                close = true;
                os << "+";
                break;
            case Sub:
                close = true;
                os << "-";
                break;
            case Assign:
                os << "=";
                close = true;
                break;
            case Const:
                break;
            case Reg:
                break;
        }


        if (close) {
            os << "(";
        }

        int i = 0;
        for (auto &item: rhs) {
            if (i++ != 0) {
                os << ", ";
            }
            item->dump(os);
        }

        if (close) {
            os << ")";
        }
    }

};

struct ItemSet {
    std::map<Symbol *, std::pair<Rule *, int>> items;

    Rule *getRule(Symbol *sym) {
        return items[sym].first;
    }

    bool contains(Symbol *sym) const {
        return items.contains(sym);
    }

    int getCost(Symbol *sym) const {
        auto iter = items.find(sym);
        if (iter == items.end()) {
            return MAX_COST;
        }
        return iter->second.second;
        //return items[sym].second;
    }

    int getMinCost() const {
        int min = MAX_COST;
        for (auto &[sym, tuple] : items) {
            if (tuple.second < min) {
                min = tuple.second;
            }
        }
        return min;
    }

    void deltaCost() {
        auto min = getMinCost();
        for (auto &[sym, tuple] : items) {
            if (tuple.second == MAX_COST) {
                continue;
            }
            tuple.second = tuple.second - min;
        }
    }

    bool add(Symbol *sym, Rule *rule, int cost) {
        if (items.contains(sym)) {

            if (cost < items[sym].second) {
                items[sym] = {rule, cost};
                return true;
            }
            return false;
        }
        return items.insert({sym, {rule, cost}}).second;
    }

    bool operator<(const ItemSet &rhs) const {
        return items < rhs.items;
    }

    void dump(std::ostream &os) const {
        std::cout << "{" << std::endl;
        for (auto &[sym, tuple]: items) {
            auto &[rule, cost] = tuple;
            sym->dump(os);
            os << "\t| ";
            if (rule) {
                rule->dump(os);
            } else {
                os << "(null)";
            }
            os << ", " << cost << std::endl;
        }
        std::cout << "}" << std::endl;

        //os << std::string(10, '-') << std::endl;

    }
};

using TransMap = std::map<Opcode, std::map<std::vector<int>, int>>;
using TransSym = std::map<Opcode, int>;

struct ISelGenerator {
    std::vector<Symbol *> terminals;
    std::vector<Symbol *> nonterminals;
    std::vector<std::unique_ptr<Rule>> rules;
    std::vector<ItemSet> worklist;
    std::map<ItemSet, int> states;
    int index = 0;
    std::set<Opcode> OP;
    TransMap theta;
    TransSym tau;
    std::map<Opcode, std::map<int, std::map<ItemSet, ItemSet>>> U;
    std::map<Opcode, std::map<int, std::set<ItemSet>>> I;

    ISelGenerator() {
        genRule();
        for (auto &rule: rules) {
            if (rule->op != None) {
                OP.insert(rule->op);
            }
        }
    }

    void genRule() {
        // terminals
        auto *Cons_t = new Symbol(Const);
        auto *Reg_t = new Symbol(Reg);
        terminals = {Cons_t, Reg_t};

        // nonterminals
        auto *reg = new Symbol("reg");
        auto *cons = new Symbol("int");
        auto *addr = new Symbol("addr");
        auto *mov = new Symbol("mov");
        nonterminals = {reg, cons, addr, mov};

        rules.emplace_back(new Rule{reg, {Reg_t}, 1});
        rules.emplace_back(new Rule{cons, {Cons_t}, 1});
        rules.emplace_back(new Rule{reg, {cons}, 1});
        //rules.emplace_back(new Rule{reg, Sub, {reg, cons}, 2});
        // rules.emplace_back(new Rule{reg, Sub, {reg, reg}, 2});
        rules.emplace_back(new Rule{reg, Add, {reg, cons}, 2});
        rules.emplace_back(new Rule{reg, Add, {reg, reg}, 2});
        rules.emplace_back(new Rule{addr, Add, {reg, cons}, 0});
        rules.emplace_back(new Rule{mov, Assign, {addr, reg}, 0});

    }

    void genRule2() {
        // terminals
        auto *cons = new Symbol(Const);
        terminals = {cons};

        // nonterminals
        auto *con = new Symbol("con");
        auto *reg = new Symbol("reg");
        auto *addr = new Symbol("addr");
        auto *stmt = new Symbol("stmt");

        nonterminals = {con, reg, addr, stmt};

        rules.emplace_back(new Rule{con, {cons}, 0});
        rules.emplace_back(new Rule{reg, {con}, 1});
        rules.emplace_back(new Rule{reg, Add, {reg, con}, 1});
        rules.emplace_back(new Rule{addr, {reg}, 0});
        rules.emplace_back(new Rule{addr, Add, {reg, con}, 0});
        rules.emplace_back(new Rule{stmt, Assign, {addr, reg}, 1});

    }

    void genRule3() {
        // terminals
        auto *Cons_t = new Symbol(Const);
        auto *Reg_t = new Symbol(Reg);
        terminals = {Cons_t, Reg_t};

        // nonterminals
        auto *reg = new Symbol("reg");
        auto *cons = new Symbol("int");
        nonterminals = {reg, cons};

        rules.emplace_back(new Rule{reg, {Reg_t}, 1});
        rules.emplace_back(new Rule{cons, {Cons_t}, 1});
        rules.emplace_back(new Rule{reg, {cons}, 1});
        rules.emplace_back(new Rule{reg, Add, {reg, cons}, 2});
        rules.emplace_back(new Rule{reg, Add, {reg, reg}, 2});

    }

    std::set<Rule *> getRules(Symbol *sym) {
        std::set<Rule *> res;
        for (auto &rule: rules) {
            if (rule->getArityZeroRHS() == sym) {
                res.insert(rule.get());
            }
        }
        return res;
    }

    std::set<Rule *> getRules(Opcode op) {
        std::set<Rule *> res;
        for (auto &rule: rules) {
            if (rule->op == op) {
                res.insert(rule.get());
            }
        }
        return res;
    }

    std::set<std::vector<ItemSet>> product(std::vector<std::set<ItemSet>> &tuple) {
        std::set<std::vector<ItemSet>> res;
        for (int i = 0; i < tuple.size(); ++i) {
            if (i == 0) {
                res = convert(tuple[i]);
            } else {
                res = product_two(res, convert(tuple[i]));
            }
        }
        return res;
    }

    std::set<std::vector<ItemSet>> convert(std::set<ItemSet> &s1) {
        std::set<std::vector<ItemSet>> res;
        for (auto &s: s1) {
            res.insert({s});
        }
        return res;
    }

    std::set<std::vector<ItemSet>> product_two(const std::set<std::vector<ItemSet>> &s1, const std::set<std::vector<ItemSet>> &s2) {
        std::set<std::vector<ItemSet>> res;
        for (auto &ss1: s1) {
            for (auto &ss2: s2) {
                auto item = ss1;
                item.insert(item.end(), ss2.begin(), ss2.end());
                res.insert(item);
            }
        }
        return res;
    }

    auto child_rules(Symbol *sym, int i) {
        std::set<Rule *> res;
        for (auto &rule : rules) {
            if (rule->op != None) {
                if (rule->rhs[i] == sym) {
                    res.insert(rule.get());
                }
            }
        }
        return res;
    }

    void closure(ItemSet &itemset) {
        bool changed;
        do {
            changed = false;
            for (auto &rule : rules) {
                auto *RHS = rule->getArityZeroRHS();
                if (itemset.items.contains(RHS)) { // is chain rule
                    int cost = rule->cost + itemset.getCost(RHS);
                    if (itemset.add(rule->getNonterminal(), rule.get(), cost)) {
                        changed = true;
                    }
                }
            }
        } while (changed);
    }

    void WorklistArityZeroTables() {
        for (auto &a: terminals) {
            ItemSet itemset;
            for (auto &rule: getRules(a)) {
                itemset.add(rule->getNonterminal(), rule, rule->cost);
            }

            itemset.deltaCost();

            closure(itemset);

            addState(itemset);
            tau[a->opcode] = states[itemset];

            std::cout << "[newstate: " << states[itemset] << "] -> " ;
            a->dump(std::cout);
            std::cout << std::endl;
            itemset.dump(std::cout);
        }
    }

    void WorklistTransition(Opcode op, ItemSet &itemset) {
        std::cout << "op -> " << getOpName(op) << std::endl;
        auto op_rules = getRules(op);
        for (int i = 0; i < getOpArity(op); ++i) {
            ItemSet repstate;
            // 对所有op中在第i维中的所有非终结符的规则在itemset(当前状态)上的投影, 取得所有可行的非终结符与推导规则, 得到表示集
            for (auto &n: nonterminals) {
                for (auto &rule: child_rules(n, i)) {
                    if (op_rules.contains(rule) && itemset.contains(n)) {
                        //repstate.add(n, rule, itemset.getCost(n));
                        repstate.add(n, itemset.items[n].first, itemset.getCost(n));
                    }
                }
            }

            std::cout << "i = " << i << std::endl;
            std::cout << "reps:" << std::endl;
            for (auto &ss: I[op][i]) {
                std::cout << findState(op, i, ss) << " -> ";
                ss.dump(std::cout);
            }

            if (repstate.items.empty()) {
                continue;
            }

            // 计算delta cost
            repstate.deltaCost();

            // 将表示集与项目集(当前状态)进行映射
            U[op][i][repstate] = itemset;

            // 如果在当前状态的表示集之前没有计算过, 就进行下一步
            if (!I[op][i].contains(repstate)) {
                std::cout << "repstate on " << states[itemset] << " :" << std::endl;
                repstate.dump(std::cout);
                I[op][i].insert(repstate); // 将表示集加入到op的第i维中的集合, 防止重复计算

                std::vector<std::set<ItemSet>> compound(getOpArity(op));
                for (int j = 0; j < getOpArity(op); ++j) {
                    if (i == j) {
                        compound[j] = {repstate};
                    } else {
                        compound[j] = I[op][j];
                    }
                }
                auto tuples = product(compound);

                for (auto &repset_tuple: tuples) {
                    ItemSet newitemset;

                    // 动态规划, 寻找op的所有规则中有最小开销的规则, 添加到新的项目集中
                    for (auto &rule: getRules(op)) {
                        int cost = rule->cost;
                        bool exist = true;
                        for (int j = 0; j < rule->rhs.size(); ++j) {
                            if (j == i) {
                                exist &= repstate.contains(rule->rhs[j]);
                                cost += repstate.getCost(rule->rhs[j]);
                            } else {
                                exist &= repset_tuple[j].contains(rule->rhs[j]);
                                cost += repset_tuple[j].getCost(rule->rhs[j]);
                            }
                        }
                        std::cout << "adding rule ";
                        rule->dump(std::cout);
                        std::cout << ", " << cost << std::endl;
                        if (exist)
                            newitemset.add(rule->getNonterminal(), rule, cost);
                    }
                    newitemset.deltaCost();

                    if (!hasState(newitemset)) {
                        closure(newitemset);
                    }

                    if (newitemset.items.empty()) {
                        /*std::cout << "[newstate: " << states_index[newitemset] << "]" << std::endl;
                        newitemset.dump(std::cout);*/
                        continue;
                    }

                    addState(newitemset);

                    std::cout << "[newstate: " << states[newitemset] << "]" << std::endl;
                    newitemset.dump(std::cout);

                    std::cout << getOpName(op);
                    std::cout << "(";
                    std::vector<int> transition;
                    int j = 0;
                    for (auto &t: repset_tuple) {
                        auto f = findState(op, j++, t);
                        transition.push_back(f);
                        std::cout << f << " ";
                    }
                    theta[op][transition] = states[newitemset];
                    std::cout << ")" << " -> " << states[newitemset] << std::endl;

                }
                std::cout << std::endl;
            }

        }
    }

    int findState(Opcode op, int i, const ItemSet &itemset) {
        auto st = U[op][i][itemset];
        if (states.contains(st)) {
            return states[st];
        }
        assert(!"not reachable");
        return -1;
    }

    bool hasState(const ItemSet &itemset) {
        return states.contains(itemset);
    }

    void addState(const ItemSet &itemset) {
        if (!states.contains(itemset)) {
            states[itemset] = ++index;
            worklist.push_back(itemset);
        }
    }

    void WorklistMain() {

        WorklistArityZeroTables();

        while (!worklist.empty()) {
            ItemSet itemset = worklist.back();
            worklist.pop_back();
            auto aa = states[itemset];
            std::cout << std::string(25, '-') << " [entering: " << aa << "] " << std::string(25, '-') << std::endl;

            for (auto &op: OP) {
                WorklistTransition(op, itemset);
            }
        }

    }

};

struct TreeNode {
    int label = 0;
    Opcode op;
    std::vector<TreeNode *> members;

    TreeNode(Opcode op) : op(op) {}

    TreeNode(const std::vector<TreeNode *> &members) : members(members) {}

    TreeNode(Opcode op, const std::vector<TreeNode *> &members) : op(op), members(members) {}

    void dump(std::ostream &os, int indent = 0) {
        os << std::string(indent * 4, ' ');
        switch (op) {
            case None:
                break;
            case Add:
                os << "+";
                break;
            case Sub:
                os << "-";
                break;
            case Assign:
                os << "=";
                break;
            case Const:
                os << "Int";
                break;
            case Reg:
                os << "Reg";
                break;
        }

        os << " (" << label << ")";

        if (members.size()) {
            os << std::endl << std::string(indent * 4, ' ') << " {" << std::endl;
            for (auto &mem: members) {
                mem->dump(os, indent + 1);
            }

            os << std::string(indent * 4, ' ') << "}";
        }

        os << std::endl;

    }

};

void automata_label(ISelGenerator &gen, TreeNode *node) {
    if (node->members.size()) {
        std::vector<int> transition;
        for (auto &mem: node->members) {
            automata_label(gen, mem);
            transition.push_back(mem->label);
        }
        node->label = gen.theta[node->op][transition];

    } else {
        node->label = gen.tau[node->op];
    }

}

template<typename K, typename V>
auto swap_mapkv(std::map<K, V> &map) {
    std::map<V, K> res;
    for (auto &[k, v]: map) {
        res[v] = k;
    }
    return res;
}

int main() {
    ISelGenerator gen;
    gen.WorklistMain();
    std::cout << std::endl << std::endl;

    std::cout << "=======================================" << std::endl;
    std::map<int, ItemSet> states;
    states = swap_mapkv(gen.states);
    for (auto &[id, itemset]: states) {
        std::cout << id << " -> ";
        itemset.dump(std::cout);
    }
    std::cout << std::endl;

    std::vector<TreeNode *> nodes = {
            new TreeNode(Assign, {new TreeNode(Add, {new TreeNode(Reg), new TreeNode(Const)}), new TreeNode(Reg)}),
            new TreeNode(Add, {new TreeNode(Add, {new TreeNode(Reg), new TreeNode(Const)}), new TreeNode(Reg)}),
            new TreeNode(Add, {new TreeNode(Reg), new TreeNode(Reg)}),
            new TreeNode(Add, {new TreeNode(Reg), new TreeNode(Const)}),
    };

    for (auto &node: nodes) {
        automata_label(gen, node);
    }

    for (auto &node: nodes) {
        node->dump(std::cout);
    }

    return 0;
}
