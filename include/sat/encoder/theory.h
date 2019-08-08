/*
 *  Copyright (C) 2011 - <date> Blai Bonet, Universidad Simon Bolivar
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

#ifndef THEORY_H
#define THEORY_H

#include <cassert>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <sat/encoder/sat.h>

namespace SAT {

int lit_var(int literal) {
    assert(literal != 0);
    return literal < 0 ? -literal - 1 : literal - 1;
}

int lit_sign(int literal) {
    assert(literal != 0);
    return literal < 0 ? -1 : 1;
}

class Theory {
  public:
    enum struct amo_encoding_t { Quad, Log, Heule };

  protected:
    const bool decode_;
    const amo_encoding_t amo_encoding_;

    std::ostream *tunnel_;
    bool weighted_max_sat_tunnel_;

    int num_implications_;
    int num_soft_implications_;

    std::vector<std::pair<int, std::string> > var_offsets_;
    std::vector<const Var*> variables_;
    std::vector<const Literal*> pos_literals_;
    std::vector<const Literal*> neg_literals_;
    std::map<std::string, int> varmap_;

    std::vector<std::pair<int, const std::string> > comments_;
    std::vector<const Implication*> implications_;
    std::vector<std::pair<int, std::string> > imp_offsets_;

    // soft clauses
    int top_soft_implications_;
    std::vector<std::pair<int, const Implication*> > soft_implications_;

    mutable bool satisfiable_;
    mutable std::vector<bool> model_;

    std::set<std::string> at_most_k_constraints_;
    std::set<std::string> at_least_k_constraints_;
    std::set<std::string> exactly_k_constraints_;

    virtual void initialize_variables() = 0;
    virtual void build_base() = 0;
    virtual void build_rest() = 0;

    // empty default builder for soft theory
    virtual void build_soft_theory() { }

    // literals
    void build_literal(int index) {
        assert(pos_literals_.size() == neg_literals_.size());
        assert((0 <= index) && (index < int(variables_.size())) && (index >= int(pos_literals_.size())));
        pos_literals_.emplace_back(new Literal(*variables_[index], false));
        neg_literals_.emplace_back(new Literal(*variables_[index], true));
    }
    void build_literals() {
        for( size_t i = 0; i < variables_.size(); ++i )
            build_literal(i);
    }

    // two comparator for *literals* x1 and y1, output *variables* in z
    void two_comparator(const std::string &prefix, int x1, int y1, std::vector<int> &z) {
        assert((x1 != 0) && (y1 != 0));

        // create new vars zmax and zmin where
        // zmax = max(x1,y1), zmin = min(x1,y1)
        int zmax = new_literal(std::string("_") + prefix + "_zmax");
        int zmin = new_literal(std::string("_") + prefix + "_zmin");
        z.emplace_back(zmax);
        z.emplace_back(zmin);

        // top three clauses (required for at-least and exactly)
        // x1 <= zmin, y1 <= zmin, x1 v y1 <= zmax
        Implication *IP1 = new Implication;
        IP1->add_antecedent(1 + zmin);
        IP1->add_consequent(x1);
        add_implication(IP1);

        Implication *IP2 = new Implication;
        IP2->add_antecedent(1 + zmin);
        IP2->add_consequent(y1);
        add_implication(IP2);

        Implication *IP3 = new Implication;
        IP3->add_antecedent(1 + zmax);
        IP3->add_consequent(x1);
        IP3->add_consequent(y1);
        add_implication(IP3);

        // bottom three clauses (required for at-most and exactly)
        // x1 => zmax, y1 => zmax, x1 & y1 => zmin
        Implication *IP4 = new Implication;
        IP4->add_antecedent(x1);
        IP4->add_consequent(1 + zmax);
        add_implication(IP4);

        Implication *IP5 = new Implication;
        IP5->add_antecedent(y1);
        IP5->add_consequent(1 + zmax);
        add_implication(IP5);

        Implication *IP6 = new Implication;
        IP6->add_antecedent(x1);
        IP6->add_antecedent(y1);
        IP6->add_consequent(1 + zmin);
        add_implication(IP6);
    }

    // merge sorted *variables* in x and y into z
    void merge_network(const std::string &prefix, const std::vector<int> &x, const std::vector<int> &y, std::vector<int> &z) {
        assert(z.empty());
        const int n = x.size();
        const int m = y.size();
        if( (n == 0) || (m == 0) ) {
            if( n == 0 )
                z = y;
            else
                z = x;
        } else if( (n == 1) && (m == 1) ) {
            two_comparator(prefix, 1 + x[0], 1 + y[0], z);
        } else {
            std::vector<int> x1, y1, z1;
            for( int i = 0; i < n; i += 2 ) x1.push_back(x[i]);
            for( int j = 0; j < m; j += 2 ) y1.push_back(y[j]);
            merge_network(prefix + "_rec1_" + std::to_string(n) + "_" + std::to_string(m), x1, y1, z1);

            std::vector<int> x2, y2, z2;
            for( int i = 1; i < n; i += 2 ) x2.push_back(x[i]);
            for( int j = 1; j < m; j += 2 ) y2.push_back(y[j]);
            merge_network(prefix + "_rec2_" + std::to_string(n) + "_" + std::to_string(m), x2, y2, z2);

            assert(int(x1.size() + x2.size()) == n);
            assert(int(y1.size() + y2.size()) == m);
            assert(z1.size() == x1.size() + y1.size());
            assert(z2.size() == x2.size() + y2.size());

            int i = 0, j = 0;
            z.emplace_back(z1[i++]);
            while( (i < int(z1.size())) && (j < int(z2.size())) )
                two_comparator(prefix + "_2cmp_" + std::to_string(n) + "_" + std::to_string(m), 1 + z2[j++], 1 + z1[i++], z);
            assert((i == int(z1.size())) || (j == int(z2.size())));
            if( i < int(z1.size()) ) z.emplace_back(z1[i++]);
            if( j < int(z2.size()) ) z.emplace_back(z2[j++]);
            assert((i == int(z1.size())) && (j == int(z2.size())));
        }
    }

    // sorting network for *literals* in x, output *variables* by decreasing value in z
    void sorting_network(const std::string &prefix, const std::vector<int> &x, std::vector<int> &z) {
        assert(z.empty());
        const int n = x.size();
        if( n == 1 ) {
            assert(x[0] != 0);
            z.emplace_back(lit_var(x[0]));
        } else if( n == 2 ) {
            assert(x[0] != 0);
            assert(x[1] != 0);
            two_comparator(prefix, x[0], x[1], z);
            assert(z.size() == 2);
        } else {
            int l = n / 2;
            assert((1 <= l) && (1 + l < n));
            std::vector<int> x1(&x[0], &x[l]), z1;
            sorting_network(prefix + "_rec1_" + std::to_string(n), x1, z1);
            assert(z1.size() == x1.size());
            std::vector<int> x2(&x[l], &x[n]), z2;
            sorting_network(prefix + "_rec2_" + std::to_string(n), x2, z2);
            assert(z2.size() == x2.size());
            assert(n == int(x1.size() + x2.size()));
            merge_network(prefix + "_merge", z1, z2, z);
            assert(z.size() == z1.size() + z2.size());
        }
    }

    void lex_ordering(const std::string &prefix,
                      const std::vector<std::vector<int> > &lvectors,
                      std::vector<int> &lex_vars);

  public:
    Theory(bool decode, amo_encoding_t amo_encoding = amo_encoding_t::Heule)
      : decode_(decode),
        amo_encoding_(amo_encoding),
        tunnel_(nullptr),
        weighted_max_sat_tunnel_(false),
        num_implications_(0),
        num_soft_implications_(0),
        top_soft_implications_(0) {
    }
    virtual ~Theory() {
        clear_implications();
        clear_soft_implications();
        clear_literals();
        clear_variables();
    }

    void build_variables() {
        std::cout << "---------------- variables + literals ---------------" << std::endl;
        initialize_variables();
        build_literals();
    }
    void build_theory() {
        std::cout << "----------------- base implications -----------------" << std::endl;
        build_base();
        build_rest();
        std::cout << "----------------- soft implications -----------------" << std::endl;
        build_soft_theory();
        std::cout << "-----------------------------------------------------" << std::endl;
    }

    // tunnel
    void set_tunnel(std::ostream *tunnel, bool weighted_max_sat_tunnel = false) {
        tunnel_ = tunnel;
        weighted_max_sat_tunnel_ = weighted_max_sat_tunnel;
    }

    // variables
    int num_variables() const {
        return variables_.size();
    }
    const Var& variable(int index) const {
        assert((0 <= index) && (index < int(variables_.size())));
        return *variables_[index];
    }
    void clear_variables() {
        for( size_t i = 0; i < variables_.size(); ++i )
            delete variables_[i];
        variables_.clear();
    }
    int new_variable(const std::string &name) {
        int index = variables_.size();
        variables_.emplace_back(new Var(index, name));
        varmap_.emplace(name, index);
        return index;
    }

    // literals
    const Literal& literal(int index) const {
        assert(index != 0);
        assert((-int(variables_.size()) <= index) && (index <= int(variables_.size())));
        return index > 0 ? *pos_literals_[index - 1] : *neg_literals_[-index - 1];
    }
    void clear_literals() {
        for( size_t i = 0; i < pos_literals_.size(); ++i )
            delete pos_literals_[i];
        pos_literals_.clear();
        for( size_t i = 0; i < neg_literals_.size(); ++i )
            delete neg_literals_[i];
        neg_literals_.clear();
    }
    int new_literal(const std::string &name) {
        int index = new_variable(name);
        build_literal(index);
        return index;
    }

    // vartypes and blocks
    void push_new_vartype(const std::string &name) {
        var_offsets_.emplace_back(variables_.size(), name);
    }
    int num_variables_in_last_block() const {
        assert(!var_offsets_.empty());
        return variables_.size() - var_offsets_.back().first;
    }
    int offset_of_last_block() const {
        assert(!var_offsets_.empty());
        return var_offsets_.back().first;
    }

    // (hard) implications
    int num_implications() const {
        return num_implications_;
    }
    const Implication* implication(int index) const {
        return implications_.at(index);
    }
    void clear_implications() {
        for( size_t i = 0; i < implications_.size(); ++i )
            delete implications_[i];
        implications_.clear();
        num_implications_ = 0;
    }
    void add_implication(const Implication *IP) {
        if( !decode_ ) {
            if( tunnel_ == nullptr ) {
                implications_.emplace_back(IP);
            } else {
                if( !weighted_max_sat_tunnel_ )
                    IP->dump(*tunnel_);
                else
                    IP->dump(*tunnel_, 999);
                delete IP;
            }
        } else {
            delete IP;
        }
        ++num_implications_;
    }

    // soft implications
    int num_soft_implications() const {
        return num_soft_implications_;
    }
    std::pair<int, const Implication*> soft_implication(int index) const {
        return soft_implications_.at(index);
    }
    void clear_soft_implications() {
        for( size_t i = 0; i < soft_implications_.size(); ++i )
            delete soft_implications_[i].second;
        soft_implications_.clear();
        top_soft_implications_ = 0;
        num_soft_implications_ = 0;
    }
    void add_soft_implication(int weight, const Implication *IP) {
        assert(weight > 0);
        if( !decode_ ) {
            if( tunnel_ == nullptr ) {
                soft_implications_.emplace_back(weight, IP);
            } else {
                assert(weighted_max_sat_tunnel_);
                IP->dump(*tunnel_, weight);
                delete IP;
            }
        } else {
            delete IP;
        }
        top_soft_implications_ += weight;
        ++num_soft_implications_;
    }
    int top_soft_implications() const {
        return top_soft_implications_;
    }

    // comments, model, satisfiable?
    void add_comment(const std::string &comment) {
        if( !decode_ ) {
            if( tunnel_ == nullptr )
                comments_.emplace_back(num_implications(), comment);
            else
                *tunnel_ << "c " << comment << std::endl;
        }
    }
    bool satisfiable() const {
        return satisfiable_;
    }
    const std::vector<bool>& model() const {
        return model_;
    }

    // get index of atom by name
    int get_atom_by_name(const std::string &literal) const {
        std::map<std::string, int>::const_iterator it = varmap_.find(literal[0] == '-' ? literal.substr(1) : literal);
        return it == varmap_.end() ? -1 : it->second;
    }

    // get literal name (string) by literal index
    std::string get_literal_by_index(int literal) const {
        int var = lit_var(literal);
        assert((var < int(pos_literals_.size())) && (var < int(neg_literals_.size())));
        const Literal *l = literal > 0 ? pos_literals_.at(var) : neg_literals_.at(var);
        assert(l != nullptr);
        return l->as_str();
    }

    // default virtual function to decode model
    void decode_model_full(std::ostream &os) const {
        for( int var = 0; var < num_variables(); ++var ) {
            if( model_.at(var) )
                os << get_literal_by_index(1 + var) << std::endl;
        }
    }
    virtual void decode_model(std::ostream &os) const {
        decode_model_full(os);
    }

    // pseudo boolean constraints
    void empty_clause() {
        add_implication(new Implication);
    }

    // AMO: quadratic encoding for constraints of the form: x0 + x1 + ... + x(n-1) <= 1
    //
    // Clauses: for 0 <= i < j < n
    //
    //   (1) -xi v -xj
    //
    // #new-vars = 0, #new-clauses = O(n^2)
    void amo_quadratic(const std::string &prefix, const std::vector<int> &literals) {
        for( int i = 0; i < int(literals.size()); ++i ) {
            assert(literals[i] != 0);
            for( int j = 1 + i; j < int(literals.size()); ++j ) {
                assert(literals[j] != 0);
                Implication *IP = new Implication;
                IP->add_antecedent(literals[i]);
                IP->add_consequent(-literals[j]);
                add_implication(IP);
            }
        }
    }

    // AMO: logarithmic encoding for constraints of the form: x0 + x1 + ... + x(n-1) <= 1
    //
    // Variables: y0, y1, ..., y(m-1) where m = ceil(log n)
    // Clauses: for 0 <= i < n, 0 <= j < m
    //
    //    (1) -xi v yj    when j-th bit of i is 1
    //    (2) -xi v -yj   otherwise
    //
    // #new-vars = O(log n), #new-clauses = O(nlog n)
    void amo_log(const std::string &prefix, const std::vector<int> &literals) {
        int m = 0;
        for( int n = literals.size(); n > 0; n = n >> 1, ++m );
        assert(((m == 0) && (literals.size() == 1)) ||
               ((m > 0) && ((1 << (m - 1)) <= int(literals.size())) && (int(literals.size()) <= (1 << m))));

        // new variables
        std::vector<int> new_vars(m, 0);
        for( int j = 0; j < m; ++j )
            new_vars[j] = new_literal(prefix + "_y" + std::to_string(j));

        // clauses
        for( int i = 0; i < int(literals.size()); ++i ) {
            for( int j = 0; j < m; ++j ) {
                int yj = 1 + new_vars[j];
                Implication *IP = new Implication;
                IP->add_antecedent(literals[i]);
                IP->add_consequent(i & (1 << j) ? yj : -yj);
                add_implication(IP);
            }
        }
    }

    // AMO: Heule encoding for constraints of the form: x0 + x1 + ... + x(n-1) <= 1
    //
    // If n <= 3, switch to quadratic encoding
    // If n > 3, create auxiliary variable y and encode the two
    // AMO constraints:
    //
    //   (1) x0 + x1 + y <= 1  (solved with quadratic encoding)
    //   (2) x2 + x3 + ... + x(n-1) + -y <= 1     (recursively)
    //
    // #new-vars = O(n), #new-clauses = O(n)
    void amo_heule(const std::string &prefix, const std::vector<int> &literals) {
        if( literals.size() < 4 ) {
            amo_quadratic(prefix, literals);
        } else {
            int y = new_literal(prefix + "_n=" + std::to_string(literals.size()));
            amo_quadratic("", {literals[0], literals[1], 1 + y});
            std::vector<int> rest(&literals[2], &literals[literals.size()]);
            rest.push_back(-(1 + y));
            amo_heule(prefix, rest);
        }
    }

    // simple constraints high-level drivers
    void at_least_1(const std::string &prefix, const std::vector<int> &literals) {
        Implication *IP = new Implication;
        for( int i = 0; i < int(literals.size()); ++i )
            IP->add_consequent(literals[i]);
        add_implication(IP);
    }
    void at_most_1(const std::string &prefix, const std::vector<int> &literals) {
        if( amo_encoding_ == amo_encoding_t::Quad )
            amo_quadratic(prefix, literals);
        else if( amo_encoding_ == amo_encoding_t::Log )
            amo_log(prefix, literals);
        else if( amo_encoding_ == amo_encoding_t::Heule )
            amo_heule(prefix, literals);
        else
            throw std::runtime_error("error: unknown encoding of AMO constraints (value=" + std::to_string(int(amo_encoding_)) + "!");
    }
    void exactly_1(const std::string &prefix, const std::vector<int> &literals) {
        at_least_1(prefix, literals);
        at_most_1(prefix, literals);
    }

    // cardinality networks
    void sorting_network_for_at_least_k(const std::string &prefix, const std::vector<int> &literals, int k) {
        // special cases
        if( k == 0 ) {
            return;
        } else if( k == 1 ) {
            Implication *IP = new Implication;
            for( size_t i = 0; i < literals.size(); ++i )
                IP->add_consequent(literals[i]);
            add_implication(IP);
            return;
        } else if( k == int(literals.size()) ) {
            for( int i = 0; i < int(literals.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(literals[i]);
                add_implication(IP);
            }
            return;
        } else if( k > int(literals.size()) ) {
            empty_clause();
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (at_least_k_constraints_.find(prefix) != at_least_k_constraints_.end()) )
            throw std::runtime_error(std::string("error: sorting network for at-least-k for '") + prefix + "' already emited!");

        // create sorting network and post constraints: z0 & z1 & ..., & z(k-1)
        std::vector<int> z;
        sorting_network(prefix, literals, z);
        assert(z.size() == literals.size());
        for( int i = 0; i < k; ++i ) {
            Implication *IP = new Implication;
            IP->add_consequent(1 + z.at(i));
            add_implication(IP);
        }
    }
    void sorting_network_for_at_most_k(const std::string &prefix, const std::vector<int> &literals, int k) {
        // special cases
        if( k == 0 ) {
            for( int i = 0; i < int(literals.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(-literals[i]);
                add_implication(IP);
            }
            return;
        } else if( k == 1 ) {
            amo_heule(prefix + "_amo_heule", literals);
            return;
        } else if ( k >= int(literals.size()) ) {
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (at_most_k_constraints_.find(prefix) != at_most_k_constraints_.end()) )
            throw std::runtime_error(std::string("error: sorting network for at-most-k for '") + prefix + "' already emited!");

        // create sorting network and post constraints: -zk & -z(k+1) & ..., & -z(last)
        std::vector<int> z;
        sorting_network(prefix, literals, z);
        assert(z.size() == literals.size());
        for( int i = k; i < int(literals.size()); ++i ) {
            Implication *IP = new Implication;
            IP->add_consequent(-(1 + z.at(i)));
            add_implication(IP);
        }
    }
    void sorting_network_for_exactly_k(const std::string &prefix, const std::vector<int> &literals, int k) {
        // special cases
        if( k == 0 ) {
            for( int i = 0; i < int(literals.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(-literals[i]);
                add_implication(IP);
            }
            return;
        } else if( k == int(literals.size()) ) {
            for( int i = 0; i < int(literals.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(literals[i]);
                add_implication(IP);
            }
            return;
        } else if( k > int(literals.size()) ) {
            empty_clause();
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (exactly_k_constraints_.find(prefix) != exactly_k_constraints_.end()) )
            throw std::runtime_error(std::string("error: sorting network for exactly-k for '") + prefix + "' already emited!");

        // create sorting network and post constraints: z0 & z1 & ... & z(k-1) & -zk & -z(k+1) & ..., & -z(last)
        std::vector<int> z;
        sorting_network(prefix, literals, z);
        assert(z.size() == literals.size());
        for( int i = 0; i < int(literals.size()); ++i ) {
            Implication *IP = new Implication;
            IP->add_consequent(i < k ? 1 + z.at(i) : -(1 + z.at(i)));
            add_implication(IP);
        }
    }

    // cardinality networks: high-level driver
    void at_least_k(const std::string &prefix, const std::vector<int> &literals, int k) {
        if( k == 1 )
            at_least_1(prefix, literals);
        else
            sorting_network_for_at_least_k(prefix, literals, k);
    }
    void at_most_k(const std::string &prefix, const std::vector<int> &literals, int k) {
        if( k == 1 )
            at_most_1(prefix, literals);
        else
            sorting_network_for_at_most_k(prefix, literals, k);
    }
    void exactly_k(const std::string &prefix, const std::vector<int> &literals, int k) {
        if( k == 1 )
            exactly_1(prefix, literals);
        else
            sorting_network_for_exactly_k(prefix, literals, k);
    }

    // lexicographic orderings
    void lex_ordering(const std::string &prefix, const std::vector<std::vector<int> > &lvectors, bool strict_order) {
        int dim = 0;
        if( lvectors.empty() ) {
            throw std::runtime_error(std::string("error: empty lvector in lexicographic ordering for '") + prefix + "'");
        } else {
            dim = lvectors.at(0).size();
            for( int i = 0; i < int(lvectors.size()); ++i ) {
                if( dim != int(lvectors.at(i).size()) ) {
                    throw std::runtime_error(std::string("error: mismatch in lvector dimension (lex for '") + prefix + "'):" +
                                             "(dim[0]=" + std::to_string(dim) + ") != " +
                                             "(dim[" + std::to_string(i) + "]=" + std::to_string(lvectors.at(i).size()) + ")");
                }
            }
            if( dim == 0 ) throw std::runtime_error(std::string("error: null dimension in lexicographic ordering for '") + prefix + "'");
        }

        std::vector<int> lex_vars;
        lex_ordering(prefix, lvectors, lex_vars);
        assert(int(lex_vars.size()) == 2 * dim * int(lvectors.size()));

        int index = strict_order ? dim * lvectors.size() : 0;
        for( int k = 0; 1 + k < int(lvectors.size()); ++k ) {
            assert(index + dim - 1 < int(lex_vars.size()));
            Implication *IP = new Implication;
            IP->add_consequent(1 + lex_vars.at(index + dim - 1));
            add_implication(IP);
            //std::cout << "OBLIGATION: " << get_literal_by_index(1 + lex_vars.at(index + dim - 1)) << std::endl;
            index += dim;
        }
    }

    // readers

    // default virtual function to read (partial) assignment from text file
    virtual std::pair<int, int> read_assignment(std::istream &is, bool skip_inexistent_atoms = false) {
        int num_lines = 0;
        int num_added_units = 0;
        std::string line;
        while( std::getline(is, line) ) {
            ++num_lines;
            if( line.empty() || (line[0] == '#') ) continue;
            bool negated = line[0] == '-';
            int atom = get_atom_by_name(line);
            if( atom == -1 ) {
                if( !skip_inexistent_atoms )
                    throw std::runtime_error(std::string("inexistent literal '") + line + "'");
                std::cout << "skipping inexistent literal '" + line + "'" << std::endl;
                continue;
            }
            int literal = negated ? -(1 + atom) : (1 + atom);
            //assert(line == get_literal_by_index(literal));
            Implication *IP = new Implication;
            IP->add_consequent(literal);
            add_implication(IP);
            ++num_added_units;
        }
        return std::make_pair(num_lines, num_added_units);
    }

    void read_model_from_vector(const std::vector<int> &literals) const {
        model_.clear();
        model_ = std::vector<bool>(num_variables(), false);
        for( size_t i = 0; i < literals.size(); ++i ) {
            int lit = literals[i];
            assert(lit != 0);
            int var = lit_var(lit);
            if( var < num_variables() ) model_.at(var) = lit > 0;
        }
    }
    void read_literals(std::istream &is, std::vector<int> &literals) const {
        for( int lit; is >> lit; ) {
            if( lit == 0 ) break;
            literals.push_back(lit);
        }
    }

    bool read_minisat_output(std::istream &is) const {
        std::vector<int> literals;
        satisfiable_ = read_minisat_output(is, literals);
        read_model_from_vector(literals);
        return satisfiable_;
    }
    bool read_minisat_output(std::istream &is, std::vector<int> &literals) const {
        bool satisfiable = false;
        std::string status;
        is >> status;
        assert((status == "SAT") || (status == "UNSAT"));
        if( status == "SAT" ) {
            satisfiable = true;
            read_literals(is, literals);
        }
        return satisfiable;
    }
    bool read_glucose_output(std::istream &is) const {
        std::vector<int> literals;
        read_literals(is, literals);
        satisfiable_ = !literals.empty();
        read_model_from_vector(literals);
        return satisfiable_;
    }

    bool read_other_output(std::istream &is) const {
        std::vector<int> literals;
        satisfiable_ = read_other_output(is, literals);
        read_model_from_vector(literals);
        return satisfiable_;
    }
    bool read_other_output(std::istream &is, std::vector<int> &literals) const {
        bool satisfiable = false;
        for( std::string line; getline(is, line); ) {
            std::istringstream iss(line);
            char line_header;
            iss >> line_header;
            if( line_header == 's' ) {
                // read status
                std::string status;
                iss >> status;
                assert((status == "SATISFIABLE") || (status == "UNSATISFIABLE"));
                satisfiable = status == "SATISFIABLE";
            } else if( line_header == 'v' ) {
                // read literals
                for( int lit; iss >> lit; ) {
                    if( lit == 0 ) break;
                    literals.push_back(lit);
                }
            }
        }
        return satisfiable;
    }

    // output
    std::string header(bool weighted_max_sat = false) const {
        if( !weighted_max_sat ) {
            assert(num_soft_implications() == 0);
            return std::string("p cnf") +
              " " + std::to_string(num_variables()) +
              " " + std::to_string(num_implications());
        } else {
            return std::string("p wcnf") +
              " " + std::to_string(num_variables()) +
              " " + std::to_string(num_implications() + num_soft_implications()) +
              " " + std::to_string(1 + top_soft_implications());
        }
    }
    void dump(std::ostream &os, bool weighted_max_sat = false) const {
        // header
        os << header(weighted_max_sat) << std::endl;

        // dump (hard) implications and comments
        size_t i = 0;
        for( int j = 0; j < num_implications(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == j) ) {
                os << "c " << comments_[i].second << std::endl;
                ++i;
            }
            if( !weighted_max_sat )
                implications_[j]->dump(os);
            else
                implications_[j]->dump(os, 1 + top_soft_implications_);
        }
        while( i < comments_.size() ) {
            os << "c " << comments_[i].second << std::endl;
            ++i;
        }

        // dump soft clauses
        if( weighted_max_sat ) {
            os << "c soft clauses" << std::endl;
            for( int j = 0; j < num_soft_implications(); ++j ) {
                int weight = soft_implications_[j].first;
                soft_implications_[j].second->dump(os, weight);
            }
        }
    }
    void print(std::ostream &os) const {
        size_t i = 0;
        for( int j = 0; j < num_implications(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == int(j)) ) {
                os << "% " << comments_[i].second << std::endl;
                ++i;
            }
            implications_[j]->print(os, pos_literals_, neg_literals_);
            os << std::endl;
        }
        while( i < comments_.size() ) {
            os << "% " << comments_[i].second << std::endl;
            ++i;
        }
    }
    void print_implications(std::ostream &os, int start, int end) const {
        while( start < end ) {
            implications_[start++]->print(os, pos_literals_, neg_literals_);
            os << std::endl;
        }
    }

    void dump_model(std::ostream &os) const {
        for( size_t var = 0; var < variables_.size(); ++var ) {
            os << variables_[var] << " ";
        }
        os << "0" << std::endl;
    }
    void print_model(std::ostream &os) const {
        for( size_t var = 0; var < model_.size(); ++var ) {
            bool sign = model_.at(var);
            if( sign ) {
                assert(var < variables_.size());
                variables_[var]->print(os);
                os << std::endl;
            }
        }
    }
};

class VarSet {
  protected:
    int base_;
    std::string varname_;
    std::vector<int> multipliers_;
    bool initialized_;
    int verbose_;

    template<typename Func, typename T, typename ...Ts>
    void enumerate_vars_helper2(std::vector<int> &tuple, Func foo, const T &first, const Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        for( size_t i = 0; i < first.size(); ++i ) {
            tuple.emplace_back(first[i]);
            enumerate_vars_helper(tuple, foo, args...);
            tuple.pop_back();
        }
    }

    template<typename Func, typename ...Ts>
    void enumerate_vars_helper(std::vector<int> &tuple, Func foo, const Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        enumerate_vars_helper2(tuple, foo, args...);
    }

    template<typename Func>
    void enumerate_vars_helper(std::vector<int> &tuple, Func foo) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        foo(*this, tuple);
    }

#if 0
    template<typename ...Ts>
    void create_vars(SAT::Theory &theory, const Ts... args) const {
        theory.push_new_vartype(varname_);
        auto foo = [&theory](const VarSet &varset, const std::vector<int> &tuple) -> void {
            std::string name = varset.varname(tuple);
            int var_index = theory.new_variable(name);
            if( varset.verbose() > 1 ) {
                std::cout << "create_var:"
                          << " name=" << name
                          << ", index=" << var_index
                          << std::endl;
            }
            assert(var_index == varset(tuple));
        };
        enumerate_vars(foo, args...);
        if( verbose_ > 0 ) {
            std::cout << varname_
                      << ": #variables=" << theory.num_variables_in_last_block()
                      << ", offset=" << theory.offset_of_last_block()
                      << std::endl;
        }
    }
#endif
    void create_vars_from_multipliers(SAT::Theory &theory, bool push_new_vartype) const {
        if( push_new_vartype ) theory.push_new_vartype(varname_);
        auto foo = [&theory](const VarSet &varset, const std::vector<int> &tuple) -> void {
            std::string name = varset.varname(tuple);
            int var_index = theory.new_variable(name);
            if( varset.verbose() > 1 ) {
                std::cout << "create_var:"
                          << " name=" << name
                          << ", index=" << var_index
                          << std::endl;
            }
            assert(var_index == varset(tuple));
        };
        enumerate_vars_from_multipliers(foo);
        if( verbose_ > 0 ) {
            std::cout << varname_
                      << ": #variables=" << theory.num_variables_in_last_block()
                      << ", offset=" << theory.offset_of_last_block()
                      << std::endl;
        }
    }

    template<typename T, typename ...Ts> int calculate_index_helper(int i, int index, T &first, Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        assert(i < int(multipliers_.size()));
        assert((0 <= first) && (first < multipliers_.at(i)));
        int new_index = index * multipliers_.at(i) + first;
        return calculate_index(1 + i, new_index, args...);
    }

    int calculate_index(int i, int index) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        assert(i == int(multipliers_.size()));
        return index;
    }

    template<typename ...Ts> int calculate_index(int i, int index, Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        return calculate_index_helper(i, index, args...);
    }

    template<typename Func>
    void enumerate_vars_from_multipliers(std::vector<int> &tuple, Func foo, int index) const {
        if( index < int(multipliers_.size()) ) {
            for( int i = 0; i < multipliers_.at(index); ++i ) {
                tuple.emplace_back(i);
                enumerate_vars_from_multipliers(tuple, foo, 1 + index);
                tuple.pop_back();
            }
        } else {
            foo(*this, tuple);
        }
    }

  public:
    VarSet(int verbose = 1) : initialized_(false), verbose_(verbose) { }
    template<typename ...Ts> VarSet(const Ts... args)
      : initialized_(false), verbose_(false) {
        fill_multipliers(args...);
    }
    virtual ~VarSet() = default;

    int base() const {
        return base_;
    }
    const std::string& varname() const {
        return varname_;
    }
    std::string varname(const std::vector<int> &tuple) const {
        std::string name(varname_);
        if( !tuple.empty() ) name += "(";
        for( size_t i = 0; i < tuple.size(); ++i ) {
            if( i > 0 ) name += ",";
            name += std::to_string(tuple[i]);
        }
        if( !tuple.empty() ) name += ")";
        return name;
    }
    const std::vector<int>& multipliers() const {
        return multipliers_;
    }
    int verbose() const {
        return verbose_;
    }
    void set_verbose(int verbose) {
        verbose_ = verbose;
    }

    template<typename T, typename ...Ts>
    void fill_multipliers(const T &first, const Ts... args) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        multipliers_.emplace_back(first.size());
        fill_multipliers(args...);
    }
    template<typename T>
    void fill_multipliers(const T &first) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        multipliers_.emplace_back(first.size());
    }

    template<typename ...Ts> void initialize(SAT::Theory &theory, const std::string &varname, Ts... args) {
        assert(!initialized_);
        base_ = theory.num_variables();
        varname_ = varname;
        fill_multipliers(args...);
        create_vars_from_multipliers(theory, true);
        initialized_ = true;
    }
    void initialize_from_multipliers(SAT::Theory &theory, const std::string &varname, bool push_new_vartype = true) {
        assert(!initialized_);
        base_ = theory.num_variables();
        varname_ = varname;
        create_vars_from_multipliers(theory, push_new_vartype);
        initialized_ = true;
    }

    template<typename Func, typename ...Ts>
    void enumerate_vars(Func foo, const Ts... args) const {
        std::vector<int> tuple;
        enumerate_vars_helper(tuple, foo, args...);
        assert(tuple.empty());
    }

    template<typename Func>
    void enumerate_vars_from_multipliers(Func foo) const {
        std::vector<int> tuple;
        enumerate_vars_from_multipliers(tuple, foo, 0);
        assert(tuple.empty());
    }

    template<typename ...Ts> int operator()(Ts... args) const {
        return base_ + calculate_index(0, 0, args...);
    }
    int operator()(const std::vector<int> &tuple) const {
        assert(multipliers_.size() == tuple.size());
        int index = 0;
        for( size_t i = 0; i < tuple.size(); ++i ) {
            assert((0 <= tuple[i]) && (tuple[i] < multipliers_.at(i)));
            index *= multipliers_.at(i);
            index += tuple[i];
        }
        return base_ + index;
    }

    void print(std::ostream &os, const std::vector<bool> &model, bool print_negative_literals = false) const {
        auto foo = [&os, model, print_negative_literals](const VarSet &varset, const std::vector<int> &tuple) -> void {
            int index = varset(tuple);
            if( model.at(index) )
                os << varset.varname(tuple) << std::endl;
            else if( print_negative_literals )
                os << "-" << varset.varname(tuple) << std::endl;
        };
        enumerate_vars_from_multipliers(foo);
    }
};

void Theory::lex_ordering(const std::string &prefix,
                          const std::vector<std::vector<int> > &lvectors,
                          std::vector<int> &lex_vars) {

    // create auxiliary variables
    std::vector<int> lvectors_indices(lvectors.size());
    std::iota(lvectors_indices.begin(), lvectors_indices.end(), 0);
    std::vector<int> dimension(lvectors.at(0).size());
    std::iota(dimension.begin(), dimension.end(), 0);

    int num_variables = variables_.size();
    VarSet Lex(lvectors_indices, dimension);
    std::string Lex_varname(std::string("Lex<") + prefix + ">");
    Lex.initialize_from_multipliers(*this, Lex_varname, false);
    while( num_variables < int(variables_.size()) )
        build_literal(num_variables++);

    VarSet SLex(lvectors_indices, dimension);
    std::string SLex_varname(std::string("SLex<") + prefix + ">");
    SLex.initialize_from_multipliers(*this, SLex_varname, false);
    while( num_variables < int(variables_.size()) )
        build_literal(num_variables++);

    // generate constraints that implement lex ordering
    auto foo = [this, &Lex, &SLex, lvectors](const SAT::VarSet &varset, const std::vector<int> &tuple) -> void {
        assert(tuple.size() == 2);
        int k = tuple.at(0);
        int j = tuple.at(1);
        if( (j > 0) && (1 + k < int(lvectors.size())) ) {
            // Lex(k,1+i) => Lex(k,i) & [ SLex(k,i) v -lit(k,1+i) v lit(1+k,1+i) ]
            // Lex(k,1+i) => Lex(k,i)
            Implication *IP1 = new Implication;
            IP1->add_antecedent(1 + Lex(k, j));
            IP1->add_consequent(1 + Lex(k, j - 1));
            add_implication(IP1);

            // Lex(k,1+i) => SLex(k,i) v -lit(k,1+i) v lit(1+k,1+i)
            Implication *IP2 = new Implication;
            IP2->add_antecedent(1 + Lex(k, j));
            IP2->add_consequent(1 + SLex(k, j - 1));
            IP2->add_consequent(-lvectors.at(k).at(j));
            IP2->add_consequent(lvectors.at(1 + k).at(j));
            add_implication(IP2);

            // SLex(k,1+i) => Lex(k,i) & [ SLex(k,i) v -lit(k,1+i) ] & [ SLex(k,i) v lit(1+k,1+i) ]
            // SLex(k,1+i) => Lex(k,i)
            Implication *IP3 = new Implication;
            IP3->add_antecedent(1 + SLex(k, j));
            IP3->add_consequent(1 + Lex(k, j - 1));
            add_implication(IP3);

            // SLex(k,1+i) => SLex(k,i) v -lit(k,1+i)
            Implication *IP4 = new Implication;
            IP4->add_antecedent(1 + SLex(k, j));
            IP4->add_consequent(1 + SLex(k, j - 1));
            IP4->add_consequent(-lvectors.at(k).at(j));
            add_implication(IP4);

            // SLex(k,1+i) => SLex(k,i) v lit(1+k,1+i)
            Implication *IP5 = new Implication;
            IP5->add_antecedent(1 + SLex(k, j));
            IP5->add_consequent(1 + SLex(k, j - 1));
            IP5->add_consequent(lvectors.at(1 + k).at(j));
            add_implication(IP5);
        } else if( 1 + k < int(lvectors.size()) ) {
            // Lex(k,0) => -lit(k,0) v lit(1+k,0)
            Implication *IP1 = new Implication;
            IP1->add_antecedent(1 + Lex(k, 0));
            IP1->add_consequent(-lvectors.at(k).at(0));
            IP1->add_consequent(lvectors.at(1 + k).at(0));
            add_implication(IP1);

            // SLex(k,0) => -lit(k,0)
            Implication *IP2 = new Implication;
            IP2->add_antecedent(1 + SLex(k, 0));
            IP2->add_consequent(-lvectors.at(k).at(0));
            add_implication(IP2);

            // SLex(k,0) => lit(1+k,0)
            Implication *IP3 = new Implication;
            IP3->add_antecedent(1 + SLex(k, 0));
            IP3->add_consequent(lvectors.at(1 + k).at(0));
            add_implication(IP3);
        }
    };
    Lex.enumerate_vars_from_multipliers(foo);

    // fill output vars
    auto bar = [&lex_vars](const VarSet &varset, const std::vector<int> &tuple) -> void {
        lex_vars.push_back(varset(tuple));
    };
    Lex.enumerate_vars_from_multipliers(bar);
    SLex.enumerate_vars_from_multipliers(bar);
}

}; // namespace SAT

#endif

