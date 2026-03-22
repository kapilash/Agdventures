#include <benchmark/benchmark.h>
#include "SmallestFree.h"
#include <numeric>

static std::vector<uint32_t> generateTestVector(size_t size, uint32_t missing) {
    // in order to be somewhat random, we can shuffle the vector after creating it
    std::vector<uint32_t> vec(size);
    for (size_t i = 0; i < size; ++i) {
        if (i < missing) {
            vec[i] = i;
        } else {
            vec[i] = i + 1; // skip the missing number
        }
    }
    auto rng = std::default_random_engine{};
    std::ranges::shuffle(vec, rng);
    return vec;
}


static void BM_SmallestFreeBV(benchmark::State& state) {
    uint32_t size = state.range(0);
    uint32_t missing = size / 2; // some number to be missing
    std::vector<uint32_t> vec = generateTestVector(size, missing);

    for (auto _ : state) {
        benchmark::DoNotOptimize(smallestFreeBV(vec));
    }
    state.SetComplexityN(size);
}


static void BM_SmallestFreeDC(benchmark::State& state) {
    uint32_t size = state.range(0);
    uint32_t missing = size / 2; // some number to be missing
    std::vector<uint32_t> vec = generateTestVector(size, missing);

    for (auto _ : state) {
        benchmark::DoNotOptimize(smallestFreeDC(vec));
    }
    state.SetComplexityN(size);
}

static void BM_SmallestFreeDCParallel(benchmark::State& state) {
    uint32_t size = state.range(0);
    uint32_t missing = size / 2; // some number to be missing
    std::vector<uint32_t> vec = generateTestVector(size, missing);

    for (auto _ : state) {
        benchmark::DoNotOptimize(smallestFreeDCParallel(vec));
    }
    state.SetComplexityN(size);
}

BENCHMARK(BM_SmallestFreeBV)->RangeMultiplier(10)->Range(1000, 1000000)->Complexity();
BENCHMARK(BM_SmallestFreeDC)->RangeMultiplier(10)->Range(1000, 1000000)->Complexity();
BENCHMARK(BM_SmallestFreeDCParallel)->RangeMultiplier(10)->Range(1000, 1000000)->Complexity();
BENCHMARK_MAIN();
