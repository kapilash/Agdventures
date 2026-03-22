#include "gtest/gtest.h"
#include "SmallestFree.h"

TEST(SmallestFreeTest, BasicTest) {
    std::vector<uint32_t> vec = {0, 1, 2, 3, 5};
    EXPECT_EQ(smallestFreeBV(vec), 4);
}


std::vector<uint32_t> generateTestVector(size_t size, uint32_t missing) {
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

TEST(SmallestFreeTest, LargeTest) {
    size_t size = 1000000; // 1 million
    uint32_t missing = 123456; // some number to be missing
    std::vector<uint32_t> vec = generateTestVector(size, missing);
    EXPECT_EQ(smallestFreeBV(vec), missing);
}

TEST(SmallestFreeTest, DivideAndConquerTest) {
    std::vector<uint32_t> vec = {0, 1, 2, 3, 5};
    EXPECT_EQ(smallestFreeDC(vec), 4);
}

TEST(SmallestFreeTest, LargeDivideAndConquerTest) {
    size_t size = 1000000; // 1 million
    uint32_t missing = 123456; // some number to be missing
    std::vector<uint32_t> vec = generateTestVector(size, missing);
    EXPECT_EQ(smallestFreeDC(vec), missing);
}

TEST(SmallestFreeTest, ParallelDivideAndConquerTest) {
    size_t size = 1000000; // 1 million
    uint32_t missing = 123456; // some number to be missing
    std::vector<uint32_t> vec = generateTestVector(size, missing);
    EXPECT_EQ(smallestFreeDCParallel(vec), missing);
}
