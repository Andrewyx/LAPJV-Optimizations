# LAPJV 

The objective of this project is to optimize the famous LAPJV algorithm in C++. 
The current C/C++ implementation is based off of https://github.com/yongyanghz/LAPJV-algorithm-c, and inspired by:
- https://github.com/google/highway
- https://github.com/src-d/lapjv
- https://agner.org/optimize/optimizing_cpp.pdf
- https://github.com/saebyn/munkres-cpp
Gemini was used in the creation of this project.

Finally, this project + compilation tweaks results in an algorithm that is over twice as fast as the original!
[Baseline](benchmarks/baseline.pdf) vs [Final](benchmarks/final.pdf) benchmarks have been included.

## Requirements
The project uses Bazel as its main build system. To use this library in your own Bazel project, add the following to your `MODULE.bazel` file:

```python
git_repository = use_repo_rule("@bazel_tools//tools/build_defs/repo:git.bzl", "git_repository")
git_repository(
    name = "lapjv",
    remote = "https://github.com/yourusername/LAPJV-Optimizations.git",
    commit = "master",
)
```

## Usage
The library provides a simple template-based API for solving the Linear Assignment Problem.

```cpp
#include "src/lap.h"
#include "src/matrix.h"

int main() {
    // Create a 5x5 cost matrix
    Matrix<double> costs(5, 5);
    // ... fill costs ...

    LAPJV<double> solver;
    solver.solve(costs);

    // After solve(), costs(i, j) will be:
    //  0.0  if row i is assigned to column j
    // -1.0  otherwise
    return 0;
}
```

### Optimization Flags
The library is augmented to automatically use high-performance flags when compiled in optimized mode. Using `-c opt` or `--config=max` will enable:
- `-O3` and `-march=native`
- `-ffast-math` and `-fopenmp-simd`
- Link-Time Optimization (`-flto`)
- SIMD acceleration via [Google Highway](https://github.com/google/highway)

## Benchmarking
To run benchmarks and compare results:

1. **Build and Run Benchmark:**
   ```bash
   bazel build --config=max //test:lapbench
   ./bazel-bin/test/lapbench --benchmark_out=results.json --benchmark_out_format=json
   ```

2. **Compare with Previous Results:**
   ```bash
   bazel run //test:compare_benchmarks -- $(pwd)/results.json
   ```

3. **Generate Visual Reports (PDF):**
   ```bash
   bazel run //test:vis_benchmark -- $(pwd)/results.json
   ```
   The reports will be saved in the `reports/` directory.

## Testing
Unit tests are written using GoogleTest and cover various edge cases including non-square matrices and large dimensions.

```bash
bazel test //test:laptest
```

## Tracing & Profiling
![Flamegraph](flamegraph/flamegraph.svg)

Trace details and symbols are only generated in debug mode. To generate a flamegraph:
1. `bazel build --config=dbg //test:lapbench`
2. `perf record -g -o flamegraph/perf.data ./bazel-bin/test/lapbench --benchmark_filter="BM_LAPJVSolve<double>/512"`
3. `perf script -i flamegraph/perf.data | stackcollapse-perf.pl | flamegraph.pl > flamegraph/flamegraph.svg`

Ensure you have the [flamegraph scripts](https://github.com/brendangregg/flamegraph) installed and in your `PATH`.