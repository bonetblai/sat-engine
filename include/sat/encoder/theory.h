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
#include <iostream>
#include <fstream>
#include <map>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <sat/encoder/sat.h>

namespace SAT {

class Theory {
  protected:
    const bool decode_;

    std::vector<std::pair<int, std::string> > var_offsets_;
    std::vector<const Var*> variables_;
    std::vector<const Literal*> pos_literals_;
    std::vector<const Literal*> neg_literals_;
    std::map<std::string, int> varmap_;

    std::vector<std::pair<int, const std::string> > comments_;
    std::vector<const Implication*> implications_;
    std::vector<std::pair<int, std::string> > imp_offsets_;

    mutable bool satisfiable_;
    mutable std::vector<bool> model_;

    std::set<std::string> at_most_k_constraints_;
    std::set<std::string> at_least_k_constraints_;
    std::set<std::string> equal_k_constraints_;

    virtual void build_variables() = 0;
    virtual void build_base() = 0;
    virtual void build_rest() = 0;

    void build_theory() {
        std::cout << "---------------- variables + literals ---------------" << std::endl;
        build_variables();
        build_literals();
        std::cout << "----------------- base implications -----------------" << std::endl;
        build_base();
        build_rest();
        std::cout << "-----------------------------------------------------" << std::endl;
    }

  public:
    Theory(bool decode) : decode_(decode) { }
    virtual ~Theory() {
        clear_implications();
        clear_literals();
        clear_variables();
    }

    // get index of atom by name
    int get_atom_by_name(const std::string &literal) const {
        std::map<std::string, int>::const_iterator it = varmap_.find(literal[0] == '-' ? literal.substr(1) : literal);
        return it == varmap_.end() ? -1 : it->second;
    }

    // get literal name (string) by literal index
    std::string get_literal_by_index(int literal) const {
        int index = literal > 0 ? literal - 1 : -literal - 1;
        const Literal *l = literal > 0 ? pos_literals_.at(index) : neg_literals_.at(index);
        assert(l != nullptr);
        return l->as_str();
    }

    // default virtual function to read (partial) model from text file
    virtual int read_symbolic_model(std::istream &is) {
        int num_added_units = 0;
        std::string line;
        while( std::getline(is, line) ) {
            //std::cout << "line=|" << line << "|" << std::flush;
            if( line.empty() || (line[0] == '#') ) continue;
            bool negated = line[0] == '-';
            int atom = get_atom_by_name(line);
            if( atom == -1 ) throw std::runtime_error(std::string("inexistent atom '") + line + "'");
            int literal = negated ? -(1 + atom) : (1 + atom);
            //std::cout << ", atom=" << atom << ", literal=|" << get_literal_by_index(literal) << "|" << std::endl;
            //assert(line == get_literal_by_index(literal));
            Implication *IP = new Implication;
            IP->add_consequent(literal);
            add_implication(IP);
            ++num_added_units;
        }
        return num_added_units;
    }

    // default virtual function to decode model
    void decode_model_full(std::ostream &os) const {
        for( int var = 0; var < num_variables(); ++var ) {
            if( model_[var] )
                os << get_literal_by_index(1 + var) << std::endl;
        }
    }
    virtual void decode_model(std::ostream &os) const {
        decode_model_full(os);
    }

    const Var& variable(int index) const {
        assert((0 <= index) && (index < int(variables_.size())));
        return *variables_[index];
    }
    const Literal& literal(int index) const {
        assert(index != 0);
        assert((-int(variables_.size()) <= index) && (index <= int(variables_.size())));
        return index > 0 ? *pos_literals_[index - 1] : *neg_literals_[-index - 1];
    }

    void clear_variables() {
        for( size_t i = 0; i < variables_.size(); ++i )
            delete variables_[i];
        variables_.clear();
    }
    void clear_literals() {
        for( size_t i = 0; i < pos_literals_.size(); ++i )
            delete pos_literals_[i];
        pos_literals_.clear();
        for( size_t i = 0; i < neg_literals_.size(); ++i )
            delete neg_literals_[i];
        neg_literals_.clear();
    }
    int num_variables() const {
        return variables_.size();
    }

    void clear_implications() {
        for( size_t i = 0; i < implications_.size(); ++i )
            delete implications_[i];
        implications_.clear();
    }
    void add_implication(const Implication *IP) {
        implications_.push_back(IP);
    }
    int num_implications() const {
        return implications_.size();
    }

    void add_comment(const std::string &comment) {
        comments_.push_back(make_pair(implications_.size(), comment));
    }

    bool satisfiable() const {
        return satisfiable_;
    }
    const std::vector<bool>& model() const {
        return model_;
    }

    void build_literal(int index) {
        assert(pos_literals_.size() == neg_literals_.size());
        assert((0 <= index) && (index < int(variables_.size())) && (index >= int(pos_literals_.size())));
        pos_literals_.push_back(new Literal(*variables_[index], false));
        neg_literals_.push_back(new Literal(*variables_[index], true));
    }
    void build_literals() {
        for( size_t i = 0; i < variables_.size(); ++i )
            build_literal(i);
    }
    int new_variable(const std::string &name) {
        int index = variables_.size();
        variables_.push_back(new Var(index, name));
        varmap_.emplace(name, index);
        if( varmap_.size() < 10 ) std::cout << "new var: " << name << " " << index << " " << varmap_.size() << std::endl;
        return index;
    }
    int new_literal(const std::string &name) {
        int index = new_variable(name);
        build_literal(index);
        return index;
    }
    void push_new_vartype(const std::string &name) {
        var_offsets_.push_back(std::make_pair(variables_.size(), name));
    }
    int num_variables_in_last_block() const {
        assert(!var_offsets_.empty());
        return variables_.size() - var_offsets_.back().first;
    }
    int offset_of_last_block() const {
        assert(!var_offsets_.empty());
        return var_offsets_.back().first;
    }

    // support for pseudo boolean constraints
    void build_2_comparator(const std::string &prefix, int x1, int y1, std::vector<int> &z) { // z1 = max(x1,y1), z2 = min(x1,y1)
        // create new vars z1 and z2
        int z1 = new_literal(std::string("_") + prefix + "_z1");
        int z2 = new_literal(std::string("_") + prefix + "_z2");
        z.push_back(z1);
        z.push_back(z2);

        // top three clauses (required for at-least and equal)
        // x1 <= z2, y1 <= z2, x1 v y1 <= z1
        Implication *IP1 = new Implication;
        IP1->add_antecedent(1 + z2);
        IP1->add_consequent(1 + x1);
        add_implication(IP1);

        Implication *IP2 = new Implication;
        IP2->add_antecedent(1 + z2);
        IP2->add_consequent(1 + y1);
        add_implication(IP2);

        Implication *IP3 = new Implication;
        IP3->add_antecedent(1 + z1);
        IP3->add_consequent(1 + x1);
        IP3->add_consequent(1 + y1);
        add_implication(IP3);

        // bottom three clauses (required for at-most and equal)
        // x1 => z1, y1 => z1, x1 & y1 => z2
        Implication *IP4 = new Implication;
        IP4->add_antecedent(1 + x1);
        IP4->add_consequent(1 + z1);
        add_implication(IP4);

        Implication *IP5 = new Implication;
        IP5->add_antecedent(1 + y1);
        IP5->add_consequent(1 + z1);
        add_implication(IP5);

        Implication *IP6 = new Implication;
        IP6->add_antecedent(1 + x1);
        IP6->add_antecedent(1 + y1);
        IP6->add_consequent(1 + z2);
        add_implication(IP6);
    }
    void build_merge_network(const std::string &prefix, int n, const std::vector<int> &x, const std::vector<int> &y, std::vector<int> &z) {
        assert((n == 1) || (n % 2 == 0));
        assert((int(x.size()) == n) && (int(y.size()) == n));
        if( n == 1 ) {
            build_2_comparator(prefix + "_base", x[0], y[0], z);
        } else {
            int m = n >> 1;
            std::vector<int> x1(m), y1(m), z1;
            std::vector<int> x2(m), y2(m), z2;
            for( int i = 0; i < m; ++i ) {
                x1[i] = x[2*i];
                y1[i] = y[2*i];
                x2[i] = x[2*i+1];
                y2[i] = y[2*i+1];
            }

            build_merge_network(prefix + "_rec" + std::to_string(m), m, x1, y1, z1);
            assert(int(z1.size()) == n);
            build_merge_network(prefix + "_rec" + std::to_string(m), m, x2, y2, z2);
            assert(int(z2.size()) == n);

            z.push_back(z1[0]);
            for( int i = 0; i < n - 1; ++i )
                build_2_comparator(prefix + "_final_" + std::to_string(i) + "of" + std::to_string(n - 1), z2[i], z1[1 + i], z);
            z.push_back(z2.back());
        }
    }
    void build_sorting_network(const std::string &prefix, int n, const std::vector<int> &x, std::vector<int> &z) {
        assert((n > 0) && (n % 2 == 0));
        assert(int(x.size()) == n);
        if( n == 2 ) {
            build_2_comparator(prefix + "_base", x[0], x[1], z);
        } else {
            int m = n >> 1;
            std::vector<int> x1(&x[0], &x[m]), z1;
            assert(int(x1.size()) == m);
            build_sorting_network(prefix + "_rec" + std::to_string(m), m, x1, z1);
            std::vector<int> x2(&x[m], &x[n]), z2;
            assert(int(x2.size()) == m);
            build_sorting_network(prefix + "_rec" + std::to_string(m), m, x2, z2);
            build_merge_network(prefix + "_merge" + std::to_string(m), m, z1, z2, z);
        }
    }
    void pad_and_build_sorting_network(const std::string &prefix, const std::vector<int> &variables, std::vector<int> &z) {
        assert(!variables.empty());
        int n = 1;
        while( n < int(variables.size()) )
            n = n << 1;

        std::vector<int> x(variables);
        while( int(x.size()) < n ) {
            // pad one var
            int index = new_literal(std::string("_") + prefix + "_pad_var" + std::to_string(x.size()));
            Implication *IP = new Implication;
            IP->add_consequent(-(1 + index));
            add_implication(IP);
            x.push_back(index);
        }
        assert(int(x.size()) == n);

        // build sorting network
        build_sorting_network(prefix + "_sort" + std::to_string(n), n, x, z);
    }

    void build_formulas_for_at_most_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        // trivial cases
        if( k == 0 ) {
            for( int i = 0; i < int(variables.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(-(1 + variables[i]));
                add_implication(IP);
            }
            return;
        } else if ( k >= int(variables.size()) ) {
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (at_most_k_constraints_.find(prefix) != at_most_k_constraints_.end()) ) {
            std::cout << "error: at-most-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

#if 0
        // provisional, direct encoding
        if( k == 1 ) {
            for( size_t i = 0; i < variables.size(); ++i ) {
                assert((0 <= variables[i]) && (variables[i] < num_variables()));
                for( size_t j = 1 + i; j < variables.size(); ++j ) {
                    Implication *IP = new Implication;
                    IP->add_consequent(-(1 + variables[i]));
                    IP->add_consequent(-(1 + variables[j]));
                    add_implication(IP);
                }
            }
        } else if( k == 2 ) {
            for( size_t i = 0; i < variables.size(); ++i ) {
                assert((0 <= variables[i]) && (variables[i] < num_variables()));
                for( size_t j = 1 + i; j < variables.size(); ++j ) {
                    for( size_t l = 0; l < variables.size(); ++l ) {
                        if( (l == i) || (l == j) ) continue;
                        Implication *IP = new Implication;
                        IP->add_antecedent(1 + variables[i]);
                        IP->add_antecedent(1 + variables[j]);
                        IP->add_consequent(-(1 + variables[l]));
                        add_implication(IP);
                    }
                }
            }
        }
#endif

        // issue constraints, handling special cases
        std::vector<int> z;
        pad_and_build_sorting_network(prefix, variables, z);

        Implication *IP = new Implication;
        IP->add_consequent(-(1 + z[k]));
        add_implication(IP);
    }
    void build_formulas_for_at_least_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= int(variables.size())));

        // trivial cases
        if( k == 0 ) {
            return;
        } else if( k == int(variables.size()) ) {
            for( int i = 0; i < int(variables.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(1 + variables[i]);
                add_implication(IP);
            }
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (at_least_k_constraints_.find(prefix) != at_least_k_constraints_.end()) ) {
            std::cout << "error: at-least-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

        // issue constraints, handling special cases
        if( k == 1 ) {
            Implication *IP = new Implication;
            for( size_t i = 0; i < variables.size(); ++i )
                IP->add_consequent(1 + variables[i]);
            add_implication(IP);
            return;
        } else {
            std::vector<int> z;
            pad_and_build_sorting_network(prefix, variables, z);

            Implication *IP = new Implication;
            IP->add_consequent(1 + z[k - 1]);
            add_implication(IP);
        }
    }
    void build_formulas_for_equal_to_k(const std::string &prefix, const std::vector<int> &variables, int k) {
        assert((0 <= k) && (k <= int(variables.size())));

        // trivial cases
        if( k == int(variables.size()) ) {
            for( int i = 0; i < int(variables.size()); ++i ) {
                Implication *IP = new Implication;
                IP->add_consequent(1 + variables[i]);
                add_implication(IP);
            }
            return;
        }

        // check that we have not already issued these constraints
        if( (prefix != "") && (equal_k_constraints_.find(prefix) != equal_k_constraints_.end()) ) {
            std::cout << "error: equal-k constraints for '" << prefix << "' already emited!" << std::endl;
            exit(0);
        }

        std::vector<int> z;
        pad_and_build_sorting_network(prefix, variables, z);

        Implication *IP1 = new Implication;
        IP1->add_consequent(-(1 + z[k]));
        add_implication(IP1);

        Implication *IP2 = new Implication;
        IP2->add_consequent(1 + z[k - 1]);
        add_implication(IP2);
    }

    // readers
    void read_minisat_output(std::ifstream &is) const {
        std::string status;
        is >> status;
        satisfiable_ = status == "SAT";
        if( satisfiable_ ) {
            int var, lit;
            model_ = std::vector<bool>(variables_.size(), false);
            for( size_t i = 0; i < variables_.size(); ++i ) {
                is >> lit;
                if( lit == 0 ) break;
                var = lit > 0 ? lit - 1 : -lit - 1;
                assert(var == int(i));
                model_[var] = lit > 0;
            }
            if( lit != 0 ) {
                is >> lit;
                assert(lit == 0);
            }
        } else {
            model_.clear();
        }
    }

    // output
    void dump(std::ostream &os) const {
        os << "p cnf " << variables_.size() << " " << implications_.size() << std::endl;
        size_t i = 0;
        for( size_t j = 0; j < implications_.size(); ++j ) {
            while( (i < comments_.size()) && (comments_[i].first == int(j)) ) {
                os << "c " << comments_[i].second << std::endl;
                ++i;
            }
            implications_[j]->dump(os);
        }
        while( i < comments_.size() ) {
            os << "c " << comments_[i].second << std::endl;
            ++i;
        }
    }
    void print(std::ostream &os) const {
        size_t i = 0;
        for( size_t j = 0; j < implications_.size(); ++j ) {
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
            bool sign = model_[var];
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

    template<typename T, typename ...Ts>
    void fill_multipliers(const T &first, const Ts... args) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        multipliers_.push_back(first.size());
        fill_multipliers(args...);
    }
    template<typename T>
    void fill_multipliers(const T &first) {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        multipliers_.push_back(first.size());
    }

    template<typename Func, typename T, typename ...Ts>
    void enumerate_vars_helper2(std::vector<int> &tuple,
                                Func foo, //void foo(const VarSet &varset, const std::vector<int> &tuple),
                                const T &first,
                                const Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        for( size_t i = 0; i < first.size(); ++i ) {
            tuple.push_back(first[i]);
            enumerate_vars_helper(tuple, foo, args...);
            tuple.pop_back();
        }
    }

    template<typename Func, typename ...Ts>
    void enumerate_vars_helper(std::vector<int> &tuple,
                               Func foo, //void foo(const VarSet &varset, const std::vector<int> &tuple),
                               const Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        enumerate_vars_helper2(tuple, foo, args...);
    }

    template<typename Func>
    void enumerate_vars_helper(std::vector<int> &tuple,
                               Func foo) const { //void foo(const VarSet &varset, const std::vector<int> &tuple)) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
#if 0 // DEPRECATED
        std::string name = varname(tuple);
        int var_index = theory.new_variable(name);
        if( verbose_ > 1 ) {
            std::cout << "create_var:"
                      << " name=" << name
                      << ", index=" << var_index
                      << std::endl;
        }
        assert(var_index == (*this)(tuple));
#endif
        foo(*this, tuple);
    }

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

    template<typename T, typename ...Ts> int calculate_index_helper(int i, int index, T &first, Ts... args) const {
        //std::cout << __PRETTY_FUNCTION__ << std::endl;
        assert(i < multipliers_.size());
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
    void enumerate_vars_from_multipliers(std::vector<int> &tuple,
                                         Func foo, //void foo(const VarSet &varset, const std::vector<int> &tuple),
                                         int index) const {
        if( index < int(multipliers_.size()) ) {
            for( size_t i = 0; i < multipliers_.at(index); ++i ) {
                tuple.push_back(i);
                enumerate_vars_from_multipliers(tuple, foo, 1 + index);
                tuple.pop_back();
            }
        } else {
            foo(*this, tuple);
        }
    }

  public:
    VarSet(int verbose = 1) : initialized_(false), verbose_(verbose) { }
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

    template<typename ...Ts> void initialize(SAT::Theory &theory, const std::string &varname, Ts... args) {
        assert(!initialized_);
        base_ = theory.num_variables();
        varname_ = varname;
        fill_multipliers(args...);
        create_vars(theory, args...);
        initialized_ = true;
    }

    template<typename Func, typename ...Ts>
    void enumerate_vars(Func foo, //void foo(const VarSet &varset, const std::vector<int> &tuple),
                        const Ts... args) const {
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

#if 0 // DEPRECATED
template<>
inline void VarSet::enumerate_vars(SAT::Theory &theory,
                                   std::vector<int> &tuple,
                                   void foo(SAT::Theory &theory, const VarSet &varset, const std::vector<int> &tuple)) const {
    //std::cout << __PRETTY_FUNCTION__ << std::endl;
#if 0 // DEPRECATED
    std::string name = varname(tuple);
    int var_index = theory.new_variable(name);
    if( verbose_ > 1 ) {
        std::cout << "create_var:"
                  << " name=" << name
                  << ", index=" << var_index
                  << std::endl;
    }
    assert(var_index == (*this)(tuple));
#endif
    foo(theory, *this, tuple);
}

template<>
inline int VarSet::calculate_index(int i, int index) const {
    //std::cout << __PRETTY_FUNCTION__ << std::endl;
    assert(i == int(multipliers_.size()));
    return index;
}
#endif

}; // namespace SAT

#endif

