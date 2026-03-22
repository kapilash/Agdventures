cmake_minimum_required(VERSION 3.25)

project(SmallestFree)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
enable_testing()
find_package(GTest CONFIG REQUIRED)
find_package(benchmark CONFIG REQUIRED)
find_package(TBB CONFIG REQUIRED)

add_executable(tests test.cpp)
target_link_libraries(tests PRIVATE GTest::gtest GTest::gtest_main GTest::gmock GTest::gmock_main)
target_link_libraries(tests PRIVATE TBB::tbb TBB::tbbmalloc)
set_property(TARGET tests PROPERTY CXX_STANDARD 23)

add_test(AllTestsInMain tests)


add_executable(benchmarks benchmark.cpp)
target_link_libraries(benchmarks PRIVATE benchmark::benchmark benchmark::benchmark_main)
target_link_libraries(benchmarks PRIVATE TBB::tbb TBB::tbbmalloc)
set_property(TARGET benchmarks PROPERTY CXX_STANDARD 23)
