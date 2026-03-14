#include <benchmark/benchmark.h>
#include <cstdlib>
#include "src/lap.h"
#include "src/matrix.h"

template <typename T>
static Matrix<T> generateRandomMatrix(int size) {
  Matrix<T> matrix(size, size);
  for (size_t row = 0; row < matrix.rows(); row++) {
    for (size_t col = 0; col < matrix.columns(); col++) {
      // This will keep decimals for float/double, and cleanly truncate for int
      matrix(row, col) = static_cast<T>(rand() % 10000) / static_cast<T>(100.0);
    }
  }
  return matrix;
}

template <typename T>
static void BM_LAPJVSolve(benchmark::State& state) {
  int dim = state.range(0);
  LAPJV<T> solver;

  srand(42);

  Matrix<T> baseline_matrix = generateRandomMatrix<T>(dim);

  for (auto _ : state) {
    Matrix<T> matrix = baseline_matrix;
    solver.solve(matrix);
  }

  state.SetComplexityN(state.range(0));
}

BENCHMARK_TEMPLATE(BM_LAPJVSolve, double)
        ->RangeMultiplier(2)
        ->Range(8, 512)
        ->Complexity(benchmark::oNCubed);

BENCHMARK_TEMPLATE(BM_LAPJVSolve, float)
        ->RangeMultiplier(2)
        ->Range(8, 512)
        ->Complexity(benchmark::oNCubed);

BENCHMARK_TEMPLATE(BM_LAPJVSolve, int)
        ->RangeMultiplier(2)
        ->Range(8, 512)
        ->Complexity(benchmark::oNCubed);

BENCHMARK_MAIN();

/*
Please use the following command to run the benchmark with optimizations and report output
 bazel build -c opt --copt="-O3" --copt="-march=native" --copt="-ffast-math" --copt="-fopenmp-simd" --copt="-flto" --linkopt="-flto" //test:lapbench
 ./bazel-bin/test/lapbench --benchmark_format=console --benchmark_out=results.json --benchmark_out_format=json

  The report json file could be found in results.json

  bazel run //test:vis_benchmark -- $(pwd)/results.json
  to visualize the benchmarks
*/