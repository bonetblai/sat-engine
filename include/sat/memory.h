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

#ifndef MEMORY_H
#define MEMORY_H

#include <algorithm>
#include <cassert>
#include <iostream>
#include <fstream>
#include <limits>
#include <math.h>
#include <set>
#include <map>
#include <vector>

namespace Memory {

template<typename T> class Pool {
  protected:
    const std::string name_;
    std::vector<std::pair<std::pair<size_t, size_t>, T*> > pool_;

    void alloc_new_block(size_t minimum_size) {
        size_t size = pool_.empty() ? 1 : (pool_.back().first.first << 1);
        assert(size > 0);
        while( size < minimum_size ) size = size << 1;
        T *block = new T[size];
        std::pair<std::pair<size_t, size_t>, T*> p(std::make_pair(size, 0), block);
        pool_.push_back(p);
    }

  public:
    Pool(const std::string &name) : name_(name) { }
    virtual ~Pool() {
        mem_stats_t stats;
        get_stats(stats);
        std::cout << "Pool: "
                  << "name='" << name_ << "', "
                  << "#blocks=" << stats.num_blocks_ << ", "
                  << "#bytes=(allocated=" << stats.bytes_allocated_ << ","
                  << "wasted=" << stats.bytes_wasted_ << ","
                  << "unused=" << stats.bytes_unused_ << ")"
                  << std::endl;
        clear();
    }

    struct mem_stats_t {
        size_t num_blocks_;
        size_t bytes_allocated_;
        size_t bytes_wasted_;
        size_t bytes_unused_;
        mem_stats_t() : num_blocks_(0), bytes_allocated_(0), bytes_wasted_(0), bytes_unused_(0) { }
    };

    void get_stats(mem_stats_t &stats, bool add = false) const {
        size_t num_blocks = pool_.size();
        size_t bytes_unused = !pool_.empty() ? (pool_.back().first.first - pool_.back().first.second) * sizeof(T) : 0;
        size_t bytes_allocated = 0;
        size_t bytes_wasted = 0;
        for( size_t i = 0; i < pool_.size(); ++i ) {
            bytes_allocated += pool_[i].first.first * sizeof(T);
            bytes_wasted += (pool_[i].first.first - pool_[i].first.second) * sizeof(T);
        }
        assert(bytes_wasted >= bytes_unused);
        bytes_wasted -= bytes_unused;

        if( !add ) {
            stats.num_blocks_ = 0;
            stats.bytes_allocated_ = 0;
            stats.bytes_wasted_ = 0;
            stats.bytes_unused_ = 0;
        }
        stats.num_blocks_ += num_blocks;
        stats.bytes_allocated_ += bytes_allocated;
        stats.bytes_wasted_ += bytes_wasted;
        stats.bytes_unused_ += bytes_unused;
    }

    void clear() {
        while( !pool_.empty() ) {
            delete[] pool_.back().second;
            pool_.pop_back();
        }
    }

    T* alloc(size_t size) {
        assert(pool_.empty() || (pool_.back().first.first >= pool_.back().first.second));
        size_t available = pool_.empty() ? 0 : pool_.back().first.first - pool_.back().first.second;
        if( available < size ) alloc_new_block(size);
        assert(pool_.back().first.first - pool_.back().first.second >= size);
        T *block = &pool_.back().second[pool_.back().first.second];
        pool_.back().first.second += size;
        return block;
    }

    T* get_block(int size) {
        int *block = alloc(1 + size);
        *block = size;
        return block;
    }
    T* get_block(const T *existing_block) {
        int block_size = *existing_block;
        T *block = get_block(block_size);
        for( int i = 1, j = 0; j < block_size; ++j )
            block[i++] = existing_block[1 + j];
        return block;
    }
    template<typename M> T* get_block(const M &container) {
        T *block = get_block(int(container.size()));
        int i = 1;
        for( typename M::const_iterator it = container.begin(); it != container.end(); ++it )
            block[i++] = *it;
        return block;
    }
    const int* get_block(const std::vector<bool> &bitmap) {
        int block_size = 0;
        for( size_t j = 0; j < bitmap.size(); ++j )
            block_size += bitmap[j] ? 1 : 0;
        int *block = get_block(block_size);
        assert(*block == block_size);
        int i = 1;
        for( size_t j = 0; j < bitmap.size(); ++j ) {
            if( bitmap[j] )
                block[i++] = j;
        }
        return block;
    }
};

}; // namespace Memory

#endif

