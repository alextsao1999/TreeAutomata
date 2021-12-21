#include <iostream>
#include <type_traits>
#include <vector>
#include <memory>
#include <map>
#include <set>
#include <cassert>
#include <algorithm>
#define INIT_COST 0
#define MAX_COST 999

enum Opcode {
    None,
    Add,
    Sub,
    Assign,
    Const,
    Reg,
};

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
        switch (opcode) {
            case None:
                os << name;
                break;
            case Const:
                os << "Int";
                break;
            case Reg:
                os << "Reg";
                break;
        }
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
    std::map<Rule *, int> rules;
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
            tuple.second = tuple.second - min;
        }
    }

    bool add(Rule *rule, int cost) {
        return rules.insert({rule, cost}).second;
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

    void dump(std::ostream &os) {
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

struct OpMap {
    std::map<int, std::map<ItemSet, ItemSet>> map;
    std::map<int, std::set<ItemSet>> reps;

};

using TransMap = std::map<Opcode, std::map<std::vector<int>, int>>;
using TransSym = std::map<Opcode, int>;

struct ISelGenerator {
    std::vector<Symbol *> terminals;
    std::vector<Symbol *> nonterminals;
    std::vector<std::unique_ptr<Rule>> rules;
    std::vector<ItemSet> worklist;
    std::set<ItemSet> states;
    std::map<ItemSet, int> states_index;
    int index = 0;
    std::set<Opcode> OP;
    TransMap theta;
    TransSym tau;
    std::map<Opcode, std::map<int, std::map<ItemSet, ItemSet>>> U;
    std::map<Opcode, std::map<int, std::set<ItemSet>>> I;

    ISelGenerator() {
        genRule3();
        for (auto &rule: rules) {
            if (rule->op != None) {
                OP.insert(rule->op);
            }
        }
    }

    void genRule() {
        // terminals
        auto *cons = new Symbol(Const);
        terminals = {cons};

        // nonterminals
        auto *reg = new Symbol("reg");
        auto *add = new Symbol("add");
        auto *addr = new Symbol("addr");
        auto *move = new Symbol("move");

        nonterminals = {reg, add, addr, move};

        rules.emplace_back(new Rule{reg, {cons}, 1});
        rules.emplace_back(new Rule{addr, {reg}, 0});
        rules.emplace_back(new Rule{addr, Add, {reg, cons}, 0});
        rules.emplace_back(new Rule{add, Add, {reg, reg}, 1});
        rules.emplace_back(new Rule{move, Assign, {addr, reg}, 1});
        rules.emplace_back(new Rule{move, Assign, {reg, reg}, 1});

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
        rules.emplace_back(new Rule{reg, Sub, {reg, cons}, 2});
        rules.emplace_back(new Rule{reg, Sub, {reg, reg}, 2});
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

    std::set<Symbol *> nt(const std::set<Rule *> &rs) {
        std::set<Symbol *> res;
        for (auto &rule: rs) {
            res.insert(rule->getNonterminal());
        }
        return res;
    }

    int getMinCost(const std::set<Rule *> &rs) {
        int min = MAX_COST;
        for (auto *rule : rs) {
            if (rule->cost < min) {
                min = rule->cost;
            }
        }
        return min;
    }

    std::set<Rule *> getChainRules(Symbol *sym) {
        std::set<Rule *> res;
        for (auto &rule : rules) {
            if (rule->getArityZeroRHS() == sym) {
                res.insert(rule.get());
            }
        }
        return getChainRules(res);
    }

    std::set<Rule *> getChainRules(const std::set<Symbol *> &syms) {
        std::set<Rule *> res;
        for (auto &rule : rules) {
            if (syms.contains(rule->getArityZeroRHS())) {
                res.insert(rule.get());
            }
        }
        return getChainRules(res);
    }

    std::set<Rule *> getChainRules(std::set<Rule *> res) {
        bool changed;
        do {
            changed = false;
            for (auto &rule : rules) {
                for (auto &n: res) {
                    if (n->getNonterminal() == rule->getArityZeroRHS()) {
                        if (res.insert(rule.get()).second) {
                            changed = true;
                        }
                    }
                    /*for (auto &arg: rule->rhs) {
                        if (n->getNonterminal() == arg) {
                            if (res.insert(rule.get()).second) {
                                changed = true;
                            }
                        }
                    }*/

                }
            }
        } while (changed);
        return res;
    }

    auto child_NT(Opcode op, int i) {
        std::set<Symbol *> res;
        for (auto &rule: rules) {
            if (rule->op == op) {
                if (rule->rhs.size() > i) {
                    res.insert(rule->rhs[i]);
                }
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

    std::map<Rule *, int> delta;
    std::map<Symbol *, int> diff;
    std::map<Opcode, std::map<int, std::map<Symbol *, int>>> indexMap;

    void IterativeArityZeroTables() {
        for (auto &a: terminals) {
            ItemSet itemset;

            auto mrules = getRules(a);
            auto mnonterminals = nt(mrules);
            auto chain_rules = getChainRules(a);
            auto match_rules = mrules;
            match_rules.insert(chain_rules.begin(), chain_rules.end());
            auto match_NT = nt(match_rules);
            // initialize cost
            for (auto *rule: match_rules) {
                delta[rule] = MAX_COST;
            }
            for (auto *nt: match_NT) {
                diff[nt] = MAX_COST;
            }

            // begin
            auto cost_min = getMinCost(mrules);
            for (auto *rule: mrules) {
                delta[rule] = rule->cost - cost_min;
            }

            for (auto *sym: mnonterminals) {
                auto min_cost = MAX_COST;
                for (auto *rule: sym->rules) {
                    if (delta.contains(rule)) {
                        if (delta[rule] < min_cost) {
                            min_cost = delta[rule];
                        }
                    }
                }
                diff[sym] = min_cost;
            }

            bool changed;
            do {
                changed = false;
                for (auto *rule: chain_rules) {
                    assert(rule->getArityZeroRHS());
                    auto &oldDn = diff[rule->getNonterminal()];
                    auto newDn = diff[rule->getArityZeroRHS()] + rule->cost;
                    if (newDn < oldDn) {
                        oldDn = newDn;
                        changed = true;
                    }

                    auto &oldDelta = delta[rule];
                    if (newDn < oldDelta) {
                        oldDelta = newDn;
                        changed = true;
                    }
                }
            } while (changed);

            for (auto *rule: match_rules) {
                itemset.add(rule, delta[rule]);
            }
            // stmt = 1, addr = 2, reg = 3, and con = 4
            states.insert(itemset);

        }
    }

    bool IterativeTransition(Opcode op, int i) {
        RepTy product = repset_product(op, i);
        RepTy sub = repset_sub(product, repset_product(op, i - 1));

        for (auto &tuple: sub) {
            ItemSet itemset;
            std::set<Rule *> mrules;
            std::map<Rule *, int> Crhs;
            std::map<Rule *, int> COST;
            for (auto &rule: rules) {
                if (op == rule->op && rule->getArity() == tuple.size()) {
                    int v = 0;
                    bool match = true;
                    int cRhsNT = 0;
                    for (auto &sym: tuple) {
                        if (sym != rule->rhs[v++]) {
                            match = false;
                            break;
                        }
                        cRhsNT += diff[sym];
                    }
                    if (match) {
                        mrules.insert(rule.get());
                        Crhs[rule.get()] = cRhsNT;
                    }
                }
            }

            auto mnonterminals = nt(mrules);
            auto chain_rules = getChainRules(mrules);
            auto match_rules = mrules;
            match_rules.insert(chain_rules.begin(), chain_rules.end());
            auto match_NT = nt(match_rules);
            // initialize cost
            for (auto *rule: match_rules) {
                delta[rule] = MAX_COST;
            }
            for (auto *nt: match_NT) {
                diff[nt] = MAX_COST;
            }

            for (auto *rule: mrules) {
                COST[rule] = Crhs[rule] + rule->cost;
            }
            int COST_Min = MAX_COST;
            for (auto *rule: mrules) {
                if (COST[rule] < COST_Min) {
                    COST_Min = COST[rule];
                }
            }
            for (auto *rule: mrules) {
                delta[rule] = COST[rule] - COST_Min;
            }

            auto getMinDeltaCost = [&](Symbol *nt) -> int {
                auto min_cost = MAX_COST;
                for (auto *rule: nt->rules) {
                    if (delta[rule] < min_cost) {
                        min_cost = delta[rule];
                    }
                }
                return min_cost;
            };

            for (auto n: mnonterminals) {
                diff[n] = getMinDeltaCost(n);
            }

            bool changed;
            do {
                changed = false;
                for (auto *rule: getChainRules(match_NT)) {
                    assert(rule->getArityZeroRHS());
                    auto &oldDn = diff[rule->getNonterminal()];
                    auto newDn = diff[rule->getArityZeroRHS()] + rule->cost;
                    if (newDn < oldDn) {
                        oldDn = newDn;
                        changed = true;
                    }

                    auto &oldDelta = delta[rule];
                    if (newDn < oldDelta) {
                        oldDelta = newDn;
                        changed = true;
                    }
                }
            } while (changed);

            auto getMinCostRule = [&](Symbol *nt) -> Rule * {
                Rule *min_rule = nullptr;
                auto min_cost = MAX_COST;
                for (auto *rule: nt->rules) {
                    if (match_rules.contains(rule) && delta[rule] < min_cost) {
                        min_cost = delta[rule];
                        min_rule = rule;
                    }
                }
                return min_rule;
            };

            for (auto *rule: match_rules) {
                //rule->getNonterminal()->rules
                auto *will = getMinCostRule(rule->getNonterminal());
                itemset.add(will, delta[will]);
            }

            int idx = 0;
            std::cout << "OP(";
            for (auto &item: tuple) {
                std::cout << indexMap[op][idx++][item] << " ";
            }
            std::cout << ")" << " -> " << states.size() << std::endl;

            states.insert(itemset);
        }

        return false;

    }

    using RepTy = std::set<std::vector<Symbol *>>;

    RepTy repset_product(Opcode op, int i) {
        RepTy product;
        if (i < 0) {
            return {};
        }
        for (int j = 0; j < getOpArity(op); ++j) {
            if (j == 0) {
                product = repset(op, j, i);
            } else {
                product = repset_product(product, repset(op, j, i));
            }
        }
        return product;
    }

    RepTy repset(Opcode op, int j, int i) {
        RepTy res;
        if (i < 0) {
            return {};
        }
        auto nts = child_NT(op, j);
        //auto &state = states[i];
        auto &state = *states.begin();
        for (auto *nt: nts) {
            for (auto &[rule, cost]: state.rules) {
                if (nt == rule->getNonterminal()) {
                    res.insert({nt});
                }
            }
        }
        return res;
    }

    RepTy repset_product(const RepTy &p1, const RepTy &p2) {
        RepTy res;
        for (auto &item1: p1) {
            for (auto &item2 : p2) {
                auto item = item1;
                item.insert(item.end(), item2.begin(), item2.end());
                res.insert(item);
            }
        }
        return res;
    }

    RepTy repset_sub(const RepTy &p1, const RepTy &p2) {
        RepTy res;
        for (auto &item: p1) {
            if (!p2.contains(item)) {
                res.insert(item);
            }
        }
        return res;
    }

    void updateIndexMap(int i) {
        if (i >= states.size()) {
            return;
        }
        for (auto op: OP) {
            for (int j = 0; j < getOpArity(op); ++j) {
                auto rep = repset(op, j, i);
                for (auto &tuple: rep) {
                    if (!indexMap[op][j].contains(tuple.front())) {

                        indexMap[op][j][tuple.front()] = i;
                    }
                }
            }
        }
    }

    void IterativeMain() {
        IterativeArityZeroTables();
        int i = 0;
        updateIndexMap(i);
        do {
            for (auto op: OP) {
                IterativeTransition(op, i);
            }
            i++;
            updateIndexMap(i);
        } while (isContinue(i));
    }

    bool isContinue(int i) {
        if (i >= states.size()) {
            return false;
        }
        bool changed = false;
        for (auto op: OP) {
            for (int j = 0; j < getOpArity(op); ++j) {
                if (repset(op, j, i) != repset(op, j, i - 1)) {
                    changed = true;
                }
            }
        }
        return changed;
    }

    void WorklistArityZeroTables() {
        for (auto &a: terminals) {
            ItemSet itemset;
            for (auto &rule: getRules(a)) {
                itemset.add(rule->getNonterminal(), rule, rule->cost);
            }

            auto min = itemset.getMinCost();
            for (auto &[sym, tuple] : itemset.items) {
                tuple.second = tuple.second - min;
            }

            bool changed;
            do {
                changed = false;
                for (auto &rule : rules) {
                    auto *RHS = rule->getArityZeroRHS();
                    if (itemset.items.contains(RHS)) { // is chain rule
                        int cost = rule->cost + itemset.items[RHS].second;

                        if (itemset.add(rule->getNonterminal(), rule.get(), cost)) {
                            changed = true;
                        }
                    }
                }
            } while (changed);

            addState(itemset);

            tau[a->opcode] = states_index[itemset];
            std::cout << "[newstate: " << states_index[itemset] << "] -> " ;
            a->dump(std::cout);
            std::cout << std::endl;

            itemset.dump(std::cout);
        }
    }

    void WorklistTransition(Opcode op, ItemSet &itemset) {
        auto op_rules = getRules(op);
        for (int i = 0; i < getOpArity(op); ++i) {
            ItemSet repstate;
            // 对当前所在的i在itemset进行投影, 取得所有可行的非终结符
            for (auto &n: nonterminals) {
                for (auto &rule: child_rules(n, i)) {
                    if (op_rules.contains(rule) && itemset.contains(n)) {
                        //repstate.add(n, rule, itemset.getCost(n));
                        repstate.add(n, itemset.items[n].first, itemset.getCost(n));
                    }
                }
            }

            // 计算delta cost
            repstate.deltaCost();
            U[op][i][repstate] = itemset;

            std::cout << "i = " << i << std::endl;
            if (!I[op][i].contains(repstate)) {
                std::cout << "repstate:" << std::endl;
                repstate.dump(std::cout);
                I[op][i].insert(repstate);

                std::vector<std::set<ItemSet>> compound(getOpArity(op));
                for (int j = 0; j < getOpArity(op); ++j) {
                    if (i == j) {
                        compound[j] = {repstate};
                    } else {
                        compound[j] = I[op][i];
                    }
                }
                auto tuples = calcProduct(compound);
                for (auto &repset_tuple: tuples) {
                    ItemSet newitemset;

                    /*if (repstate.items.size() == 0) {
                        continue;
                    }*/

                    for (auto &rule: getRules(op)) {
                        int cost = rule->cost;
                        for (int j = 0; j < rule->rhs.size(); ++j) {
                            if (j == i) {
                                cost += repstate.getCost(rule->rhs[j]);
                            } else {
                                cost += repset_tuple[j].getCost(rule->rhs[j]);
                            }
                        }
                        newitemset.add(rule->getNonterminal(), rule, cost);
                    }
                    newitemset.deltaCost();

                    if (!states.contains(newitemset)) {
                        bool changed;
                        do {
                            changed = false;
                            for (auto &rule: getRules(op)) {
                                if (newitemset.items.contains(rule->getArityZeroRHS())) {
                                    int cost = rule->cost + newitemset.getCost(rule->getArityZeroRHS());
                                    if (newitemset.add(rule->getNonterminal(), rule, cost)) {
                                        changed = true;
                                    }
                                }
                            }
                        } while (changed);
                    }

                    addState(newitemset);


                    std::cout << "[newstate: " << states_index[newitemset] << "]" << std::endl;
                    newitemset.dump(std::cout);

                    int idx = 0;
                    switch (op) {
                        case None:
                            break;
                        case Add:
                            std::cout << "+";
                            break;
                        case Sub:
                            std::cout << "-";
                            break;
                        case Assign:
                            std::cout << "=";
                            break;
                        case Const:
                            break;
                        case Reg:
                            break;
                    }
                    std::cout << "(";
                    std::vector<int> transition;
                    for (auto &t: repset_tuple) {
                        transition.push_back(findState(op, i, t));
                        auto f = findState(op, i, t);
                        std::cout << f << " ";
                    }
                    theta[op][transition] = states_index[newitemset];
                    std::cout << ")" << " -> " << states_index[newitemset] << std::endl;
                    std::cout << std::endl;

                }
            }
            //repstate.deltaCost();


        }
    }

    int findState(Opcode op, int i, const ItemSet &itemset) {
        auto st = U[op][i][itemset];
        if (states_index.contains(st)) {
            return states_index[st];
        }
        return -1;
    }

    void addState(const ItemSet &itemset) {
        if (states.insert(itemset).second) {
            states_index[itemset] = ++index;
        }
        //worklist.insert(worklist.begin(), itemset);
        worklist.push_back(itemset);
    }

    std::set<std::vector<ItemSet>> calcProduct(std::vector<std::set<ItemSet>> &tuple) {
        std::set<std::vector<ItemSet>> res;
        for (int i = 0; i < tuple.size(); ++i) {
            if (i == 0) {
                res = trans(tuple[i]);
            } else {
                res = calcTwo(res, trans(tuple[i]));
            }
        }
        return res;
    }

    std::set<std::vector<ItemSet>> trans(std::set<ItemSet> &s1) {
        std::set<std::vector<ItemSet>> res;
        for (auto &s: s1) {
            res.insert({s});
        }
        return res;
    }

    std::set<std::vector<ItemSet>> calcTwo(const std::set<std::vector<ItemSet>> &s1, const std::set<std::vector<ItemSet>> &s2) {
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

    void WorklistMain() {

        WorklistArityZeroTables();

        while (!worklist.empty()) {
            ItemSet itemset = worklist.back();
            worklist.pop_back();
            auto aa = states_index[itemset];
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

void automata_label(TransMap &theta, TransSym &tau, TreeNode *node) {
    if (node->members.size()) {
        std::vector<int> tran;
        for (auto &mem: node->members) {
            automata_label(theta, tau, mem);
            tran.push_back(mem->label);
        }
        node->label = theta[node->op][tran];

    } else {
        node->label = tau[node->op];
    }


}

int main() {
    ISelGenerator gen;
    gen.WorklistMain();

    auto *node = new TreeNode(Add, {new TreeNode(Sub, {new TreeNode(Reg), new TreeNode(Const)}), new TreeNode(Reg)});

    automata_label(gen.theta, gen.tau, node);

    node->dump(std::cout);
    //gen.IterativeMain();


    return 0;
}
