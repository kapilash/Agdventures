#pragma once

#include <cstdint>
#include <vector>
#include <algorithm>
#include <random>
#include <span>
#include <execution>

inline uint32_t smallestFreeBV(const std::vector<uint32_t>& vec) {
 std::vector<bool> bitVector(vec.size(), false);
    for (int num : vec) {
        if (num < bitVector.size()) {
            bitVector[num] = true;
        }
    }
    for (std::size_t i = 0; i < bitVector.size(); ++i) {
        if (!bitVector[i]) {
            return static_cast<uint32_t>(i);
        }
    }
    return static_cast<uint32_t>(bitVector.size());
}


inline uint32_t smallestFrom(std::span<uint32_t> xs, uint32_t a) {
    if (xs.empty()) {
        return  a;
    }
    const size_t n = xs.size();
    // pivot is low + half the range size + 1
    const size_t b = a + 1 + static_cast<uint32_t>(n / 2);

    // In-place partitioning:  us = [x for x in xs if x < b], vs = [x for x in xs if x >= b]
    auto mid_it = std::ranges::partition(xs, [b](uint32_t x) { return x < b; }).begin();
    const size_t m = std::distance(xs.begin(), mid_it);

     if (m == (b - a)) {
        // All numbers in the range [a, b) are present, so the smallest missing number is in the upper half
        return smallestFrom(xs.subspan(m), b);
     } else {
         return smallestFrom(xs.subspan(0, m), a);
     }
} 

inline uint32_t smallestFreeDC(std::vector<uint32_t>& vec) {
    return smallestFrom(std::span(vec), 0);
}

inline uint32_t smallestFromParallel(std::span<uint32_t> xs, uint32_t a) {
    if (xs.empty()) {
        return  a;
    }
    
    const size_t n = xs.size();
    if (n < 100000) {
          return smallestFrom(xs, a); // for small sizes, the overhead of parallelism may outweigh the benefits.
    }

    // pivot is low + half the range size + 1
    const size_t b = a + 1 + static_cast<uint32_t>(n / 2);

    // In-place partitioning:  us = [x for x in xs if x < b], vs = [x for x in xs if x >= b]
    auto mid_it = std::partition(std::execution::par_unseq, xs.begin(), xs.end(), 
                                 [b](uint32_t x) { return x < b; });


    const size_t m = std::distance(xs.begin(), mid_it);

     if (m == (b - a)) {
        // All numbers in the range [a, b) are present, so the smallest missing number is in the upper half
        return smallestFromParallel(xs.subspan(m), b);
     } else {
         return smallestFromParallel(xs.subspan(0, m), a);
     }
}

inline uint32_t smallestFreeDCParallel(std::vector<uint32_t>& vec) {
    return smallestFromParallel(std::span(vec), 0);
}
