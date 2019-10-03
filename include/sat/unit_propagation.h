/*
 *  Copyright (C) Blai Bonet
 *
 *  Permission is hereby granted to distribute this software for
 *  non-commercial research purposes, provided that this copyright
 *  notice is included with any such distribution.
 *
 *  THIS SOFTWARE IS PROVIDED "AS IS" WITHOUT WARRANTY OF ANY KIND,
 *  EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO, THE
 *  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 *  PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE
 *  SOFTWARE IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU
 *  ASSUME THE COST OF ALL NECESSARY SERVICING, REPAIR OR CORRECTION.
 *
 *  Blai Bonet, bonet@ldc.usb.ve, bonetblai@gmail.com
 *
 */

#ifndef UNIT_PROPAGATION_H
#define UNIT_PROPAGATION_H

#include <algorithm>
#include <deque>
#include <iostream>
#include <map>
#include <random>
#include <set>
#include <string>
#include <vector>
#include <sat/memory.h>

//#define DEBUG
//#define OLD_WATCHED

namespace SAT {

using Mempool = Memory::Pool<int>;
class WatchedLiteralsUP;

enum dump_format_t { weighted = 1, partial = 2 };

class Assignment : public std::vector<int> {
  protected:
    int num_assigned_;

  public:
    Assignment() : num_assigned_(0) { }
    bool is_unassigned(int literal) const {
        return at(abs(literal)) == -1;
    }
    bool is_true(int literal) const {
        assert(at(abs(literal)) != -1);
        return literal > 0 ? at(abs(literal)) == 1 : at(abs(literal)) == 0;
    }
    bool is_false(int literal) const {
        assert(at(abs(literal)) != -1);
        return literal > 0 ? at(abs(literal)) == 0 : at(abs(literal)) == 1;
    }

    int num_assigned() const {
        return num_assigned_;
    }
    void increase_assigned() {
        ++num_assigned_;
    }
    void decrease_assigned() {
        --num_assigned_;
    }

    std::string as_string() const {
        std::string str("{");
        bool need_comma = false;
        for( int i = 1; i < int(size()); ++i ) {
            if( (at(i) != -1) && (at(i) == 1) ) {
                if( need_comma ) str += ",";
                if( at(i) == 0 ) str += "-";
                str += std::to_string(i);
                need_comma = true;
            }
        }
        return str + "}";
    }
    friend std::ostream& operator<<(std::ostream &os, const Assignment &assignment) {
        return os << assignment.as_string() << std::flush;
    }
};

class NewClause {
  protected:
    int *clause_; // this belongs to memory pool

  public:
    NewClause() noexcept : clause_(nullptr) { }
    NewClause(NewClause &&clause) noexcept {
        clause_ = clause.clause_;
        clause.clause_ = nullptr;
    }
    template<typename T> NewClause(Mempool &mempool, const T &clause) noexcept {
        clause_ = mempool.get_block(clause);
    }
    explicit NewClause(Mempool &mempool, std::initializer_list<int> &&ilist) noexcept {
        std::vector<int> clause(std::move(ilist));
        clause_ = mempool.get_block(clause);
    }
    explicit NewClause(Mempool &mempool, int literal) noexcept {
        clause_ = mempool.alloc(2);
        clause_[0] = 1;
        clause_[1] = literal;
    }
    explicit NewClause(Mempool &mempool, int l1, int l2) noexcept {
        clause_ = mempool.alloc(3);
        clause_[0] = 2;
        clause_[1] = l1;
        clause_[2] = l2;
    }

    bool empty() const noexcept {
        assert((clause_ != nullptr) && (*clause_ >= 0));
        return *clause_ == 0;
    }
    bool unit() const noexcept {
        return size() == 1;
    }
    int size() const noexcept {
        assert((clause_ != nullptr) && (*clause_ >= 0));
        return *clause_;
    }

    int at(int i) const {
        if( (i < 0) || (i >= size()) )
            throw std::runtime_error(std::string("index ") + std::to_string(i) + " out of bounds");
        else
            return (*this)[i];
    }
    int operator[](int i) const noexcept {
        return clause_[1 + i];
    }
    int& operator[](int i) noexcept {
        return clause_[1 + i];
    }

    std::string as_string() const noexcept {
        std::string str("{");
        for( int k = 0; k < size(); ++k ) {
            str += std::to_string((*this)[k]);
            if( 1 + k < size() ) str += ",";
        }
        return str + "}";
    }
    friend std::ostream& operator<<(std::ostream &os, const NewClause &clause) {
        return os << clause.as_string() << std::flush;
    }

    void dump(std::ostream &os, dump_format_t format, int top_cost = 0) const {
        if( (format & dump_format_t::weighted) || (format & dump_format_t::partial) )
            os << top_cost << " ";
        for( int i = 0; i < *clause_; ++i )
            os << clause_[1 + i] << " ";
        os << 0 << std::endl;
    }
};

class OldClause : public std::vector<int> {
  public:
    OldClause() = default;
    OldClause(int n, int literal) {
        assign(n, literal);
    }
    OldClause(OldClause &&clause) = default;
    OldClause(const std::vector<int> &clause) {
        insert(end(), clause.begin(), clause.end());
    }
    OldClause(const std::set<int> &clause) {
        insert(end(), clause.begin(), clause.end());
    }
    OldClause(std::initializer_list<int> &&ilist) : std::vector<int>(std::move(ilist)) {
    }

    bool unit() const {
        return size() == 1;
    }

    int add(int literal) {
        assert(literal != 0);
        emplace_back(literal);
        return int(size()) - 1;
    }

    std::string as_string() const {
        std::string str("{");
        for( size_t k = 0; k < size(); ++k ) {
            str += std::to_string((*this)[k]);
            if( 1 + k < size() ) str += ",";
        }
        return str + "}";
    }
    friend std::ostream& operator<<(std::ostream &os, const OldClause &clause) {
        return os << clause.as_string() << std::flush;
    }

    void dump(std::ostream &os, dump_format_t format, int top_cost = 0) const {
        if( (format & dump_format_t::weighted) || (format & dump_format_t::partial) )
            os << top_cost << " ";
        for( int i = 0; i < int(size()); ++i )
            os << (*this)[i] << " ";
        os << 0 << std::endl;
    }
};

using Clause = NewClause;
class CNF : public std::vector<Clause> {
  protected:
    int max_var_index_;

  public:
    CNF() : max_var_index_(-1) { }
    CNF(const CNF &cnf) = default;
    CNF(CNF &&cnf) = default;

    int num_variables() const {
        return 1 + max_var_index_;
    }
    int num_clauses() const {
        return size();
    }

    int max_var_index() const {
        return max_var_index_;
    }
    int max_literal_index() const {
        return 2 * (1 + max_var_index_);
    }
    int literal_index(int literal) const {
        return (literal < 0 ? 1 + max_var_index_ : 0) +  abs(literal);
    }
    int get_literal_from_literal_index(int literal_index) const {
        return literal_index <= (1 + max_var_index_) ? literal_index : -(literal_index - (1 + max_var_index_));
    }

    void set_max_var_index(int max_var_index) {
        assert(max_var_index_ <= max_var_index);
        max_var_index_ = max_var_index;
    }
    int new_var_index() {
        return ++max_var_index_;
    }

#if 0
    int calculate_max_var_index(size_t start = 0) {
        max_var_index_ = 0;
        for( size_t i = start; i < size(); ++i ) {
            const Clause &cl = (*this)[i];
            for( size_t j = 0; j < cl.size(); ++j ) {
                int index = abs(cl[j]);
                max_var_index_ = std::max<int>(index, max_var_index_);
            }
        }
        return max_var_index_;
    }
#endif

    size_t add_clause(Mempool &mempool, const std::vector<int> &clause, std::default_random_engine *random_engine = nullptr) {
        size_t index = size();
        Clause cl(mempool, clause);
        if( random_engine != nullptr )
            std::shuffle(&cl[0], &cl[cl.size()], *random_engine);
        emplace_back(std::move(cl));
        return index;
    }
    size_t add_clause(Mempool &mempool, const std::vector<int> &clause, std::default_random_engine &random_engine) {
        return add_clause(mempool, clause, &random_engine);
    }
    size_t add_clause(Clause &&clause, std::default_random_engine *random_engine = nullptr) {
        size_t index = size();
        if( random_engine != nullptr )
            std::shuffle(&clause[0], &clause[clause.size()], *random_engine);
        emplace_back(std::move(clause));
        return index;
    }
    size_t add_clause(Clause &&clause, std::default_random_engine &random_engine) {
        return add_clause(std::move(clause), &random_engine);
    }

    std::string as_string() const {
        std::string str("{");
        for( size_t k = 0; k < size(); ++k ) {
            str += (*this)[k].as_string();
            if( 1 + k < size() ) str += ",";
        }
        return str + "}";
    }
    friend std::ostream& operator<<(std::ostream &os, const CNF &cnf) {
        return os << cnf.as_string() << std::flush;
    }

    void dump_header(std::ostream &os, dump_format_t format, int num_variables, int num_clauses, int top_cost) const {
        // format: http://www.maxsat.udl.cat/08/index.php?disp=requirements
        if( (format & dump_format_t::weighted) || (format & dump_format_t::partial) ) {
            os << "p wcnf " << num_variables << " " << num_clauses;
            if( format & dump_format_t::partial ) os << " " << top_cost;
            os << std::endl;
        } else {
            os << "p cnf " << num_variables << " " << num_clauses << std::endl;
        }
    }
    void dump(std::ostream &os, dump_format_t format, int num_additional_soft_clauses = 0, int top_cost = 0) const {
        // format: http://www.maxsat.udl.cat/08/index.php?disp=requirements

        // dump header
        dump_header(os, format, num_variables(), num_clauses() + num_additional_soft_clauses, top_cost);

        // dump clauses
        for( int i = 0; i < num_clauses(); ++i )
            (*this)[i].dump(os, format, top_cost);
    }
};

class ImplicationGraph {
  protected:
    const CNF &cnf_;
    int decision_level_;

    // first indexed by decision-index and stores pairs (literal,dec-level),
    // second stores for each decision level, all decision indices
    std::vector<std::pair<int, int> > implied_literals_;
    std::vector<std::vector<int> > implied_literals_by_decision_level_;

    // both indexed by literal indices: first store parents of nodes
    // in graph, second stores (node) indices into implied_literals_
    // invariant: implied_literals_[node_indices_[literal_index]].first == literal
    std::vector<std::vector<int> > node_parents_;
    std::vector<int> node_indices_;

  public:
    ImplicationGraph(const CNF &cnf) : cnf_(cnf), decision_level_(-1) {
        reset();
    }
    ~ImplicationGraph() { }

    void reset() {
        decision_level_ = -1;
        node_indices_ = std::vector<int>(1 + cnf_.max_literal_index(), -1);
        node_parents_ = std::vector<std::vector<int> >(1 + cnf_.max_literal_index());
    }

    // query
    bool conflict() const {
        return node_indices_[0] != -1;
    }
    int decision_level() const {
        return decision_level_;
    }
    bool non_empty_decision_level() const {
        return (decision_level_ > -1) && !implied_literals_by_decision_level_.back().empty();
    }
    std::pair<int, int> last_implied_literal() const {
        assert(non_empty_decision_level());
        return implied_literals_.back();
    }

    // increase / decrease decision level
    void increase_decision_level() {
        assert(int(implied_literals_by_decision_level_.size()) == 1 + decision_level_);
        implied_literals_by_decision_level_.emplace_back();
        ++decision_level_;
    }
    void decrease_decision_level(bool force = false) {
        assert(decision_level_ > -1);
        assert(int(implied_literals_by_decision_level_.size()) == 1 + decision_level_);
        assert(force || implied_literals_by_decision_level_.back().empty());
        implied_literals_by_decision_level_.pop_back();
        --decision_level_;
    }

    // backtracks
    int backtrack_last_implied_literal(Assignment &assignment, WatchedLiteralsUP &wlup); 
    int backtrack_until_decision_level(Assignment &assignment, WatchedLiteralsUP &wlup, int dlevel);

    // add nodes to graph
    int add_conflict_node(const std::vector<std::pair<int, int> > &watched, const Assignment &assignment, int clause_index, int implied_literal) {
        assert(node_indices_[0] == -1);
        assert(decision_level_ >= 0);
        assert(int(implied_literals_by_decision_level_.size()) == 1 + decision_level_);

#ifdef DEBUG
        std::cout << "add_conflict_node:"
                  << " implied_literal=" << implied_literal
                  << ", clause[" << clause_index << "]=" << (clause_index == -1 ? std::string("<decision>") : cnf_[clause_index].as_string())
                  << ", dl=" << decision_level_
                  << std::endl;
#endif

        assert((clause_index == -1) || (cnf_.at(clause_index).at(watched.at(clause_index).second) == implied_literal));
        assert(assignment.is_true(-implied_literal));
        int comp_implied_literal_index = cnf_.literal_index(-implied_literal);
        assert(node_indices_.at(comp_implied_literal_index) != -1);

        // add conflict node
        int implied_literal_index = cnf_.literal_index(implied_literal);
        assert(node_indices_.at(implied_literal_index) == -1);
        int implied_literal_node_index = add_implied_literal(watched, assignment, clause_index, implied_literal);
        assert(node_indices_.at(implied_literal_index) == implied_literal_node_index);
        int conflict_node_index = implied_literals_.size();
        implied_literals_by_decision_level_.back().push_back(conflict_node_index);
        node_indices_[0] = conflict_node_index;
        node_parents_[0].push_back(implied_literal_index);
        node_parents_[0].push_back(comp_implied_literal_index);
        implied_literals_.push_back(std::make_pair(0, decision_level_));
        return conflict_node_index;
    }

    int add_implied_literal(const std::vector<std::pair<int, int> > &watched, const Assignment &assignment, int clause_index, int implied_literal) {
        assert(decision_level_ >= 0);
        assert(int(implied_literals_by_decision_level_.size()) == 1 + decision_level_);

#ifdef DEBUG
        std::cout << "add_implied_literal:"
                  << " implied_literal=" << implied_literal
                  << ", clause[" << clause_index << "]=" << (clause_index == -1 ? std::string("<decision>") : cnf_[clause_index].as_string())
                  << ", dl=" << decision_level_
                  << std::endl;
#endif

        // if decison, clause index is -1. Otherwise, it is always the case that decision is made for second watched literal
        assert((clause_index == -1) || (cnf_.at(clause_index).at(watched.at(clause_index).second) == implied_literal));
        assert((clause_index == -1) || (cnf_.at(clause_index).size() >= 1));

        // calculate index for literal
        int implied_literal_index = cnf_.literal_index(implied_literal);
        assert(node_indices_.at(implied_literal_index) == -1);
        assert(node_parents_.at(implied_literal_index).empty());

        // add implied literal
        int node_index = implied_literals_.size();
        node_indices_[implied_literal_index] = node_index;
        implied_literals_by_decision_level_.back().push_back(node_index);
        implied_literals_.push_back(std::make_pair(implied_literal, decision_level_));

        // add edges to implication graph
        if( clause_index != -1 ) {
            node_parents_[implied_literal_index].reserve(int(cnf_[clause_index].size()) - 1);

            bool found = false;
            for( int i = 0; i < int(cnf_[clause_index].size()); ++i ) {
                int literal = cnf_[clause_index][i];
                if( literal != implied_literal ) {
                    assert(assignment.is_false(literal));
                    int comp_literal_index = cnf_.literal_index(-literal);
                    assert(node_indices_.at(comp_literal_index) != -1);
                    node_parents_[implied_literal_index].push_back(comp_literal_index);
                } else {
                    found = true;
                }
            }
            assert(found);
        }
        return node_index;
    }

    // compute conflict clause
    void backward_reachability_analysis(const Assignment &assignment, std::vector<int> &roots, int node_index, bool negate_literals) const {
        assert(implied_literals_[node_index].first == 0); // conflict node
        std::vector<bool> backward_reachable(1 + cnf_.max_literal_index(), false);
        std::deque<int> queue;
        queue.push_back(node_index);
        while( !queue.empty() ) {
            int node_index = queue.back();
            queue.pop_back();
            int literal = implied_literals_[node_index].first;
            int level = implied_literals_[node_index].second;
            int literal_index = cnf_.literal_index(literal);
            if( (level > 0) && !backward_reachable[literal_index] ) {
                backward_reachable[literal_index] = true;
                if( node_parents_[literal_index].empty() ) {
                    roots.push_back(negate_literals ? -literal : literal);
                } else {
                    for( int i = 0; i < int(node_parents_[literal_index].size()); ++i ) {
                        int parent_literal_index = node_parents_[literal_index][i];
                        queue.push_back(node_indices_[parent_literal_index]);
                    }
                }
            }
        }
    }

    void compute_last_uip_conflict_clause_v2(const Assignment &assignment, std::vector<int> &conflict_clause, bool negate_literals) const {
        assert(conflict());
        assert(!implied_literals_by_decision_level_.empty());
        assert(implied_literals_by_decision_level_.back().size() > 1);
        backward_reachability_analysis(assignment, conflict_clause, node_indices_[0], negate_literals);
    }
    void compute_last_uip_conflict_clause(const Assignment &assignment, std::vector<int> &conflict_clause, bool negate_literals) const {
        assert(conflict());
        assert(!implied_literals_by_decision_level_.empty());
        assert(implied_literals_by_decision_level_.back().size() > 1);

        // create conflict side of last-uip cut
        const std::vector<int> &current_decision_level = implied_literals_by_decision_level_.back();
        assert(node_parents_.at(cnf_.literal_index(implied_literals_.at(current_decision_level.at(0)).first)).empty());
        std::vector<int> conflict_side(&current_decision_level[1], &current_decision_level[current_decision_level.size()]);
        int decision_literal = implied_literals_[current_decision_level[0]].first;

        // nodes in reason side with arcs into conflict side
        std::set<int> selected;
        for( int i = 0; i < int(conflict_side.size()); ++i ) {
            int node_index = conflict_side[i];
            int literal = implied_literals_[node_index].first;
            int literal_index = cnf_.literal_index(literal);
            for( int j = 0; j < int(node_parents_[literal_index].size()); ++j ) {
                int parent_literal_index = node_parents_[literal_index][j];
                int parent_literal = implied_literals_[node_indices_[parent_literal_index]].first;
                int parent_literal_level = implied_literals_[node_indices_[parent_literal_index]].second;
                if( (parent_literal_level > 0) && ((parent_literal_level < decision_level_) || (parent_literal == decision_literal)) ) {
                    // add this literal
                    selected.insert(negate_literals ? -parent_literal : parent_literal);
                }
            }
        }
        conflict_clause.insert(conflict_clause.end(), selected.begin(), selected.end());
    }
    void analyze_conflict(const Assignment &assignment, std::vector<int> &conflict_clause, bool negate_literals) const {
        assert(conflict());
        compute_last_uip_conflict_clause_v2(assignment, conflict_clause, negate_literals);
    }

    void dump_dot(std::ostream &os, const Assignment &assignment) const {
        os << "digraph dfa {" << std::endl;

        // vertices
        for( int i = 0; i < int(implied_literals_.size()); ++i ) {
            int literal = implied_literals_[i].first;
            int level = implied_literals_[i].second;
            os << "    q" << i
               << " [label=\"" << (literal == 0 ? "nil" : std::to_string(literal))
               << "/" << level
               << "\"];"
               << std::endl;
        }

        // arrows
        for( int i = 0; i < int(implied_literals_.size()); ++i ) {
            int literal = implied_literals_[i].first;
            int literal_index = cnf_.literal_index(literal);
            for( int j = 0; j < int(node_parents_[literal_index].size()); ++j ) {
                int parent_literal_index = node_parents_[literal_index][j];
                assert(node_indices_.at(parent_literal_index) != -1);
                int k = node_indices_[parent_literal_index];
                os << "    q" << k << " -> q" << i << ";" << std::endl;
            }
        }
        os << "}" << std::endl;
    }

    void stats(std::ostream &os) const {
        os << "graph: dl=" << decision_level_
           << ", #implied-literals=" << implied_literals_.size()
           << std::endl;
    }
};

class WatchedLiteralsUP {
  protected:
    const CNF &cnf_;
    const bool track_satisfied_clauses_;

    std::vector<std::vector<int> > literal_to_clause_indices_; // clause indices where literal appears
    std::vector<std::pair<int, int> > watched_;                // 2 watched literals in clause
    std::vector<int> satisfied_;                               // number of true (satisfied) literals in clause

    // true if given literal is being watched in given clause index
    bool is_watched(int clause_index, int literal) const {
        return (literal == cnf_[clause_index][watched_[clause_index].first]) ||
               (literal == cnf_[clause_index][watched_[clause_index].second]);
    }

    // clause indices where given literal is being watched
    void clauses_where_literal_is_watched(int literal, std::vector<int> &clause_indices) const {
        assert(clause_indices.empty());
        int literal_index = cnf_.literal_index(literal);
        assert((0 < literal_index) && (literal_index < int(literal_to_clause_indices_.size())));
        for( int k = 0; k < int(literal_to_clause_indices_[literal_index].size()); ++k ) {
            int clause_index = literal_to_clause_indices_[literal_index][k];
            if( is_watched(clause_index, literal) )
                clause_indices.push_back(clause_index);
        }
    }

    // find new watched literal in given clause (index), after first watched literal now evaluates to false
    int find_replacement(const Assignment &assignment, int clause_index) const {
        int clause_size = int(cnf_[clause_index].size());
        assert((clause_size == 1) || (watched_.at(clause_index).first != watched_.at(clause_index).second));
        assert(assignment.is_false(cnf_.at(clause_index).at(watched_.at(clause_index).first)));
        if( clause_size > 2 ) {
            int w2 = watched_[clause_index].second;
#ifdef OLD_WATCHED
            for( int w1 = 0; w1 < clause_size; ++w1 ) {
                if( (w1 != w2) && (assignment.is_unassigned(cnf_[clause_index][w1]) || assignment.is_true(cnf_[clause_index][w1])) )
                    return w1;
            }
#else
            for( int w1_end = watched_[clause_index].first, w1 = (1 + w1_end) % clause_size; w1 != w1_end; w1 = (1 + w1) % clause_size ) {
                if( (w1 != w2) && (assignment.is_unassigned(cnf_[clause_index][w1]) || assignment.is_true(cnf_[clause_index][w1])) )
                    return w1;
            }
#endif
        }
        return -1;
    }

    // var has just been assigned, propagate its value
    // returns true if new value can be propagated without generating unsat clause
    bool propagate(Assignment &assignment, int var, ImplicationGraph &graph) {
        std::deque<int> queue;

        // enqueue literal for value of (just assigned) var
        queue.push_back(get_literal_from_assignment(assignment, var));
        while( !graph.conflict() && !queue.empty() ) {
            int literal = queue.back();
            queue.pop_back();

            int comp_literal_index = cnf_.literal_index(-literal);
            for( int k = 0; !graph.conflict() && (k < int(literal_to_clause_indices_[comp_literal_index].size())); ++k ) {
                int clause_index = literal_to_clause_indices_[comp_literal_index][k];
                if( !is_watched(clause_index, -literal) || (satisfied_[clause_index] > 0) ) continue;
                assert(watched_.at(clause_index).first < int(cnf_.at(clause_index).size()));

                // swap watched literals (if needed) so that first one corresponds to -literal
                if( cnf_[clause_index][watched_[clause_index].first] != -literal )
                    std::swap(watched_[clause_index].first, watched_[clause_index].second);
                assert(cnf_.at(clause_index).at(watched_.at(clause_index).first) == -literal);

                // find new watched literal (if possible); results is either w1 != -1 if w1 != w2 and w1 can
                // be watched or clause is satisfied by w1, or w1 == -1 if no other watched literal can be found
                int w1 = find_replacement(assignment, clause_index);
                int w2 = watched_[clause_index].second;

                // if w1 cannot be replaced and w2 is unassigned, recursive call
                int alt_watched_literal = cnf_[clause_index][w2];
                if( w1 != -1 ) {
                    // update first watched literal in clause
                    assert((w1 != w2) && (assignment.is_unassigned(cnf_[clause_index][w1]) || assignment.is_true(cnf_[clause_index][w1])));
                    watched_[clause_index].first = w1;
                } else if( assignment.is_unassigned(alt_watched_literal) ) {
                    // alt_watched_literal is currently unassigned, force its value
                    // (implied by unit clause) and continue propagation (recursively)
                    assert(satisfied_[clause_index] == 0);
                    set_assignment(assignment, alt_watched_literal);
                    assert(!track_satisfied_clauses_ || (satisfied_[clause_index] == 1));
                    graph.add_implied_literal(watched_, assignment, clause_index, alt_watched_literal);
                    queue.push_back(alt_watched_literal);
                } else if( assignment.is_false(alt_watched_literal) ) {
                    // if w1 cannot be replaced and w2 is false there is a conflict
                    graph.add_conflict_node(watched_, assignment, clause_index, alt_watched_literal);
                }
            }
        }
        return !graph.conflict();
    }
    bool propagate_rec(Assignment &assignment, int var, ImplicationGraph &graph, int depth = 0) {
        // get literal and its complement from value of (just assigned) var
        int literal = get_literal_from_assignment(assignment, var);
        int comp_literal_index = cnf_.literal_index(-literal);
        for( int k = 0; !graph.conflict() && (k < int(literal_to_clause_indices_[comp_literal_index].size())); ++k ) {
            int clause_index = literal_to_clause_indices_[comp_literal_index][k];
            if( !is_watched(clause_index, -literal) || (satisfied_[clause_index] > 0) ) continue;
            assert(watched_.at(clause_index).first < int(cnf_.at(clause_index).size()));

            // swap watched literals (if needed) so that first one corresponds to -literal
            if( cnf_[clause_index][watched_[clause_index].first] != -literal )
                std::swap(watched_[clause_index].first, watched_[clause_index].second);
            assert(cnf_.at(clause_index).at(watched_.at(clause_index).first) == -literal);

            // find new watched literal (if possible); results is either w1 != -1 if w1 != w2 and w1 can
            // be watched or clause is satisfied by w1, or w1 == -1 if no other watched literal can be found
            int w1 = find_replacement(assignment, clause_index);
            int w2 = watched_[clause_index].second;

            // if w1 cannot be replaced and w2 is unassigned, recursive call
            int alt_watched_literal = cnf_[clause_index][w2];
            if( w1 != -1 ) {
                // update first watched literal in clause
                assert((w1 != w2) && (assignment.is_unassigned(cnf_[clause_index][w1]) || assignment.is_true(cnf_[clause_index][w1])));
                watched_[clause_index].first = w1;
            } else if( assignment.is_unassigned(alt_watched_literal) ) {
                // alt_watched_literal is currently unassigned, force its value
                // (implied by unit clause) and continue propagation (recursively)
                assert(satisfied_[clause_index] == 0);
                set_assignment(assignment, alt_watched_literal);
                assert(!track_satisfied_clauses_ || (satisfied_[clause_index] == 1));
                graph.add_implied_literal(watched_, assignment, clause_index, alt_watched_literal);
                if( !propagate_rec(assignment, abs(alt_watched_literal), graph, 1 + depth) )
                    assert(graph.conflict());
            } else if( assignment.is_false(alt_watched_literal) ) {
                // if w1 cannot be replaced and w2 is false there is a conflict
                graph.add_conflict_node(watched_, assignment, clause_index, alt_watched_literal);
            }
        }
        return !graph.conflict();
    }

  public:
    WatchedLiteralsUP(const CNF &cnf, bool track_satisfied_clauses = false)
      : cnf_(cnf), track_satisfied_clauses_(track_satisfied_clauses) {
    }
    virtual ~WatchedLiteralsUP() { }

    bool empty() const {
        return watched_.empty();
    }
    int size() const {
        return watched_.size();
    }

    void print_literal_to_clause_indices(std::ostream &os) const {
        for( int k = 1; k < int(literal_to_clause_indices_.size()); ++k ) {
            os << cnf_.get_literal_from_literal_index(k) << " ->";
            const std::vector<int> &clause_indices = literal_to_clause_indices_[k];
            for( int j = 0; j < int(clause_indices.size()); ++j ) {
                os << " " << cnf_[clause_indices[j]];
                if( 1 + j < int(clause_indices.size()) ) os << ",";
            }
            os << std::endl;
        }
    }

#if 0
    float score(int literal) const {
        int n = 0;
        int size = 0;
        for( int i = 0; i < int(literal_to_clause_indices_[cnf_.literal_index(literal)].size()); ++i ) {
            int clause_index = literal_to_clause_indices_[cnf_.literal_index(literal)][i];
            if( satisfied_[clause_index] == 0 ) {
                size += int(cnf_[clause_index].size());
                ++n;
            }
        }
        return (float)size / (float)n;
    }
#endif

    void extend_literal_to_clause_indices(size_t starting_clause_index = 0) {
        literal_to_clause_indices_.resize(1 + cnf_.max_literal_index());
        for( int k = starting_clause_index; k < int(cnf_.size()); ++k ) {
            const Clause &clause = cnf_[k];
            for( int j = 0; j < int(clause.size()); ++j ) {
                int literal = clause[j];
                literal_to_clause_indices_[cnf_.literal_index(literal)].push_back(k);
            }
        }
    }
    void initialize_data_structures(Assignment &assignment, size_t starting_clause_index = 0) {
        extend_literal_to_clause_indices(starting_clause_index);
        for( int k = starting_clause_index; k < int(cnf_.size()); ++k ) {
            const Clause &clause = cnf_[k];
            assert(!clause.empty());
#ifdef OLD_WATCHED
            watched_.push_back(std::make_pair(0, clause.size() - 1));
#else
            watched_.push_back(std::make_pair(0, 1 % clause.size()));
#endif
        }

        // mark every variable as unassigned
        // var-index = n -> pos-literal = 1 + n -> assignment.sz >= 2 + n
        assignment.assign(2 + cnf_.max_var_index(), -1);
        satisfied_.assign(cnf_.num_clauses(), 0);
    }
    void adjust_data_structures(const Assignment &assignment, size_t starting_clause_index) {
        assert(int(assignment.size()) == 2 + cnf_.max_var_index());
        assert(watched_.size() == starting_clause_index);

        satisfied_.resize(cnf_.num_clauses());
        extend_literal_to_clause_indices(starting_clause_index);
        for( int k = starting_clause_index; k < int(cnf_.size()); ++k ) {
            const Clause &clause = cnf_[k];
            assert(!clause.empty());
#ifdef OLD_WATCHED
            watched_.push_back(std::make_pair(0, clause.size() - 1));
#else
            watched_.push_back(std::make_pair(0, 1 % clause.size()));
#endif

            satisfied_[k] = 0;
            if( track_satisfied_clauses_ ) {
                for( int i = 0; i < int(clause.size()); ++i )
                    satisfied_[k] += !assignment.is_unassigned(clause[i]) && assignment.is_true(clause[i]) ? 1 : 0;
            }
        }
    }

    // caller must increase decision level in graph before making the call
    bool make_decision(Assignment &assignment, ImplicationGraph &graph, int literal) {
        if( assignment.is_unassigned(literal) ) {
            set_assignment(assignment, literal);
            graph.add_implied_literal(watched_, assignment, -1, literal);
            return propagate(assignment, abs(literal), graph);
        } else if( assignment.is_false(literal) ) {
            graph.add_conflict_node(watched_, assignment, -1, literal);
            return false;
        } else {
            assert(assignment.is_true(literal));
            return true;
        }
    }

    // caller must increase decision level in graph before making the call
    // data structures must have been initialized/adjusted before call
    std::pair<bool, std::pair<int, int> > resolve_unit_clauses(Assignment &assignment, ImplicationGraph &graph, size_t starting_clause_index = 0, bool verbose = false) {
        assert(cnf_.empty() || (starting_clause_index < cnf_.size()));
        assert(!graph.conflict());

        int num_unit_clauses = 0;
        int num_propagated_units = 0;
        for( size_t k = starting_clause_index; k < cnf_.size(); ++k ) {
            const Clause &clause = cnf_[k];
            assert(!clause.empty());
            int literal = clause[0];
            if( clause.unit() ) {
                ++num_unit_clauses;
                if( assignment.is_unassigned(literal) ) {
                    ++num_propagated_units;
                    if( !make_decision(assignment, graph, literal) ) {
                        assert(graph.conflict());
                        return std::make_pair(false, std::make_pair(0, 0));
                    }
                } else if( assignment.is_false(literal) ) {
                    return std::make_pair(false, std::make_pair(0, 0));
                }
            }
        }

        if( verbose && (num_unit_clauses > 0) ) {
            std::cout << "resolve_unit_clauses:"
                      << " #units=" << num_unit_clauses
                      << ", #propagated=" << num_propagated_units
                      << ", #assigned=" << assignment.num_assigned()
                      << std::endl;
        }

        return std::make_pair(!graph.conflict(), std::make_pair(num_unit_clauses, num_propagated_units));;
    }

    // set/unset value of literal
    void set_assignment(Assignment &assignment, int literal) {
        assert(assignment.is_unassigned(literal));
        if( track_satisfied_clauses_ ) {
            int literal_index = cnf_.literal_index(literal);
            for( int i = 0; i < int(literal_to_clause_indices_[literal_index].size()); ++i )
                ++satisfied_[literal_to_clause_indices_[literal_index][i]];
        }
        assignment[abs(literal)] = literal > 0 ? 1 : 0;
        assignment.increase_assigned();
    }
    void unset_assignment(Assignment &assignment, int literal) {
        assert(assignment.is_true(literal) || assignment.is_false(literal));
        if( assignment.is_true(literal) ) {
            if( track_satisfied_clauses_ ) {
                int literal_index = cnf_.literal_index(literal);
                for( int i = 0; i < int(literal_to_clause_indices_[literal_index].size()); ++i ) {
                    --satisfied_[literal_to_clause_indices_[literal_index][i]];
                    assert(satisfied_[literal_to_clause_indices_[literal_index][i]] >= 0);
                }
            }
            assignment[abs(literal)] = -1;
            assignment.decrease_assigned();
        }
    }
    int get_literal_from_assignment(Assignment &assignment, int var) {
        assert((0 < var) && (var < int(assignment.size())));
        assert(!assignment.is_unassigned(var));
        return assignment[var] ? var : -var;
    }

    // backtracks
    void backtrack_last_implied_literal(Assignment &assignment, ImplicationGraph &graph) {
        assert(graph.non_empty_decision_level());
        graph.backtrack_last_implied_literal(assignment, *this);
    }
    int backtrack_last_decision_level(Assignment &assignment, ImplicationGraph &graph) {
        int decision_level = graph.decision_level();
        while( decision_level == graph.decision_level() )
            backtrack_last_implied_literal(assignment, graph);;
        assert(decision_level == 1 + graph.decision_level());
        return graph.decision_level();
    }
    int backtrack_until_decision_level(Assignment &assignment, ImplicationGraph &graph, int decision_level) {
#if 0
        assert(decision_level <= graph.decision_level());
        while( decision_level < graph.decision_level() )
            backtrack_last_decision_level(assignment, graph);
        assert(decision_level == graph.decision_level());
        return graph.decision_level();
#else
        return graph.backtrack_until_decision_level(assignment, *this, decision_level);
#endif
    }

#if 0
    void restore(size_t start) {
        watched_.erase(watched_.begin() + start, watched_.end());

        // remove references to removed clauses
        for( size_t k = 0; k < var_to_clauses_map_.size(); ++k ) {
            std::vector<int> &map = var_to_clauses_map_[k];
            for( size_t j = 0; j < map.size(); ++j ) {
                if( map[j] >= int(start) ) {
                    map[j] = map.back();
                    map.pop_back();
                    --j;
                }
            }
        }
    }

    bool lookahead(const CNF &cnf, std::vector<int> &assigned, ImplicationGraph &graph) {
        std::vector<int> copy;
        for( size_t var = 1; var < assigned.size(); ++var ) {
            if( assigned[var] != -1 ) continue; // var is already assigned
            copy = assigned;
            copy[var] = 1; // try UP with var = true
            if( !propagate(cnf, copy, var, graph) ) { // propagating with copy
                assigned[var] = 0; // because var = true results in inconsistent theory
                if( !propagate(cnf, assigned, var, graph) )
                    return false; // indicates that the CNF is inconsistent
            } else {
                copy = assigned;  // getting back original assigned
                copy[var] = 0; // try UP with var = false
                if( !propagate(cnf, copy, var, graph) ) {
                    assigned[var] = 1; // because var = false results in inconsistent theory
                    if( !propagate(cnf, assigned, var, graph) )
                        return false; // indicates that the CNF is inconsistent
                }
            }
        }
        return true; // indicates no inconsistency found
    }
#endif
};

inline int ImplicationGraph::backtrack_last_implied_literal(Assignment &assignment, WatchedLiteralsUP &wlup) {
    assert(non_empty_decision_level());
    int node_index = int(implied_literals_.size()) - 1;
    int literal = implied_literals_.back().first;
    int level = implied_literals_.back().second;
    int literal_index = cnf_.literal_index(literal);
    assert(decision_level_ == level);
    assert(node_indices_[literal_index] == node_index);
    node_parents_[literal_index].clear();
    node_indices_[literal_index] = -1;
    assert(implied_literals_by_decision_level_.back().back() == node_index);
    implied_literals_.pop_back();
    implied_literals_by_decision_level_.back().pop_back();
    if( implied_literals_by_decision_level_.back().empty() ) decrease_decision_level();
    if( literal != 0 ) wlup.unset_assignment(assignment, literal);
    return literal;
}

inline int ImplicationGraph::backtrack_until_decision_level(Assignment &assignment, WatchedLiteralsUP &wlup, int dlevel) {
    if( !implied_literals_.empty() ) {
        int boundary = 0;
        while( (boundary < int(implied_literals_.size())) && (implied_literals_[boundary].second <= dlevel) )
            ++boundary;
        assert((boundary == int(implied_literals_.size())) || (implied_literals_[boundary].second > dlevel));
        for( int i = boundary; i < int(implied_literals_.size()); ++i ) {
            assert(implied_literals_[i].second > dlevel);
            int literal = implied_literals_[i].first;
            int literal_index = cnf_.literal_index(literal);
            assert(node_indices_[literal_index] == i);
            node_parents_[literal_index].clear();
            node_indices_[literal_index] = -1;
            if( (literal != 0) && !assignment.is_unassigned(literal) )
                wlup.unset_assignment(assignment, literal);
        }
        implied_literals_.resize(boundary);
    }
    while( decision_level() > dlevel ) decrease_decision_level(true);
    return decision_level();
}

}; // namespace SAT

#undef DEBUG

#endif

