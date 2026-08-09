import Benchmark.Hardness.Inputs.StageP.Inputs
import ComplexityReduction.Agent.Hardness.ModelAuthoring
import ComplexityReduction.AxiomGate
import ComplexityReduction.Program.List

namespace StagePExperiment

open ComplexityReduction
open ComplexityReduction.Encoding
open ComplexityReduction.Program
open ComplexityReduction.Agent.Hardness.Authoring

abbrev source := Benchmark.Hardness.Inputs.StageP.Inputs.singleSemanticSource
abbrev target := Benchmark.Hardness.Inputs.StageP.Inputs.singleSemanticTarget

abbrev edgePresentation : LawfulEncodedType :=
  StandardInstances.prod StandardInstances.unaryNat StandardInstances.unaryNat

noncomputable def program : PolyProg source.representation target.representation :=
  .comp (PolyProg.listCons edgePresentation)
    (.pair (.const source.representation edgePresentation ((0 : Nat), (0 : Nat)))
      (.id source.representation))

theorem program_run (edges : source.Instance) :
    program.run edges = ((0 : Nat), (0 : Nat)) :: edges :=
  rfl

theorem semantic : ProgramSemanticProof source target program := by
  intro edges
  change edges.length % 5 = 1 ↔ (((0 : Nat), (0 : Nat)) :: edges).length % 5 = 2
  simp only [List.length_cons]
  omega

noncomputable def reduction : ComplexityReduction.Certificate.CertifiedReduction source target where
  program := program
  correct := semantic

end StagePExperiment

assert_standard_axioms StagePExperiment.program, StagePExperiment.semantic,
  StagePExperiment.reduction
