import Benchmark.Hardness.Inputs.StageP.Inputs

/-!
Small compile targets for the P-A patch-envelope qualification.

These probes are not reduction capabilities and are never published to the
runtime registry.  They only let the contract runner verify that a fresh model
response is valid Lean syntax of the promised broad shape before Stage P's
real candidate compiler exists.
-/

namespace Benchmark.Hardness.Inputs.StageP.ContractProbes

def proofProbe : Prop := ∀ value : Bool, value = value

abbrev programProbe : Type := Nat → Nat

def presentationProbe : Prop := ∀ values : List Bool, values = values

def directTMProbe : Prop := ∀ value : Nat, value ≤ value

def membershipProbe : Prop := ∀ value : Nat, value = value

def completenessProbe : Prop := True

end Benchmark.Hardness.Inputs.StageP.ContractProbes
