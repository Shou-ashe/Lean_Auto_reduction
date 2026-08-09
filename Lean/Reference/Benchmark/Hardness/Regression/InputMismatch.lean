import Benchmark.Hardness.Inputs.Negative.NoRoute

/-!
The declarations elaborate independently, while the benchmark InputGate fixes
their direction and exact endpoint before probing.  The executable regression
for the missing path lives in the `no-route` benchmark case.
-/

#check Benchmark.Hardness.Inputs.Negative.NoRoute.source
#check Benchmark.Hardness.Inputs.Negative.NoRoute.target
