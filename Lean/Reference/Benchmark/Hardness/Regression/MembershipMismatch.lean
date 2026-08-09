import Benchmark.Hardness.Inputs.Negative.BackendOnlyMembership
import Benchmark.Hardness.Inputs.Negative.WrongMembership

/-!
These intentionally non-matching declarations must remain importable so the
generated Goal can reject them at the exact `NativeTMInNP source` boundary.
-/

#check Benchmark.Hardness.Inputs.Negative.WrongMembership.wrongMembership
#check Benchmark.Hardness.Inputs.Negative.BackendOnlyMembership.backendOnlyMembership
