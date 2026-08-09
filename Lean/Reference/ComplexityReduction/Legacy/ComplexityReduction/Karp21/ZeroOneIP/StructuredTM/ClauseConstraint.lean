import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.PrefixRow
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.Bound

namespace ComplexityReduction
namespace Karp21
namespace ZeroOneIP

open ComplexityReduction.Combinatorics

def clauseConstraintInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat clauseStructuredEncodedType

abbrev ClauseConstraintInput := Nat × SAT.Clause

def clauseConstraintFromInput (p : ClauseConstraintInput) : List Int × Int :=
  let q := clausePrefixFromClause p.2
  (prefixRowRunner (p.1, q), prefixBound q)

theorem clauseConstraintFromInput_eq_clauseConstraint
    (p : ClauseConstraintInput) (hlen : p.2.length ≤ 3) :
    clauseConstraintFromInput p = clauseConstraint p.1 p.2 := by
  rcases p with ⟨n, c⟩
  simp [clauseConstraintFromInput, clauseConstraint, prefixRowRunner_eq_prefixRow,
    prefixRow_clausePrefix_eq_clauseRow n hlen, prefixBound_clausePrefix_eq_clauseBound hlen]

theorem clauseConstraintFromInput_tm_polytime :
    TMPolyTimeMap
      clauseConstraintInputEncodedType
      constraintStructuredEncodedType
      clauseConstraintFromInput := by
  let X := clauseConstraintInputEncodedType
  have hN : TMPolyTimeMap X EncodedType.nat (fun p : ClauseConstraintInput => p.1) := by
    simpa [X, clauseConstraintInputEncodedType, ClauseConstraintInput] using
      TMPolyTimeMap.fst EncodedType.nat clauseStructuredEncodedType
  have hClause : TMPolyTimeMap X clauseStructuredEncodedType
      (fun p : ClauseConstraintInput => p.2) := by
    simpa [X, clauseConstraintInputEncodedType, ClauseConstraintInput] using
      TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
  have hPrefix : TMPolyTimeMap X clausePrefixStateEncodedType
      (fun p : ClauseConstraintInput => clausePrefixFromClause p.2) := by
    have hComp := TMPolyTimeMap.comp clausePrefixFromClause_tm_polytime hClause
    simpa [Function.comp, X] using hComp
  have hRowInput :
      TMPolyTimeMap X prefixRowInputEncodedType
        (fun p : ClauseConstraintInput => (p.1, clausePrefixFromClause p.2)) :=
    TMPolyTimeMap.prod_mk hN hPrefix
  have hRow : TMPolyTimeMap X intRowStructuredEncodedType
      (fun p : ClauseConstraintInput => prefixRowRunner (p.1, clausePrefixFromClause p.2)) := by
    have hComp := TMPolyTimeMap.comp prefixRowRunner_tm_polytime hRowInput
    simpa [Function.comp, prefixRowInputEncodedType, X] using hComp
  have hBound : TMPolyTimeMap X EncodedType.int
      (fun p : ClauseConstraintInput => prefixBound (clausePrefixFromClause p.2)) := by
    have hComp := TMPolyTimeMap.comp prefixBound_tm_polytime hPrefix
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hRow hBound
  simpa [clauseConstraintFromInput, constraintStructuredEncodedType, X] using hOut

theorem prefixBound_inputSize_le_five (q : ClausePrefixState) :
    EncodedType.int.inputSize (prefixBound q) ≤ 5 := by
  have hBound :
      -((3 : Nat) : Int) ≤ prefixBound q ∧ prefixBound q ≤ ((3 : Nat) : Int) := by
    rcases q with ⟨count, l0, l1, l2⟩
    cases count with
    | zero =>
        simp [prefixBound]
    | succ count =>
        cases count with
        | zero =>
            cases l0 with
            | mk var0 neg0 =>
                cases neg0 <;> simp [prefixBound, prefixBoundOneFromNeg]
        | succ count =>
            cases count with
            | zero =>
                cases l0 with
                | mk var0 neg0 =>
                    cases l1 with
                    | mk var1 neg1 =>
                        cases neg0 <;> cases neg1 <;>
                          simp [prefixBound, prefixBoundTwoFromNegs]
            | succ count =>
                cases l0 with
                | mk var0 neg0 =>
                    cases l1 with
                    | mk var1 neg1 =>
                        cases l2 with
                        | mk var2 neg2 =>
                            cases neg0 <;> cases neg1 <;> cases neg2 <;>
                              simp [prefixBound, prefixBoundThreeFromNegs]
  exact intStructured_inputSize_le_five_of_between_three hBound.1 hBound.2

theorem prefixRow_length (n : Nat) (q : ClausePrefixState) :
    (prefixRow n q).length = n := by
  induction n with
  | zero =>
      simp [prefixRow, prefixRowFrom]
  | succ n ih =>
      simp [prefixRow_succ_append, ih]

theorem prefixRow_entries_inputSize_le (n : Nat) (q : ClausePrefixState) :
    ∀ z ∈ prefixRow n q, EncodedType.int.inputSize z ≤ 5 := by
  intro z hz
  induction n with
  | zero =>
      simp [prefixRow, prefixRowFrom] at hz
  | succ n ih =>
      rw [prefixRow_succ_append] at hz
      rcases List.mem_append.mp hz with hzOld | hzLast
      · exact ih hzOld
      · simp at hzLast
        rcases hzLast with rfl
        have hBound := prefixCoeffAt_bound q n
        exact intStructured_inputSize_le_five_of_between_three hBound.1 hBound.2

theorem prefixRowRunner_inputSize_le (n : Nat) (q : ClausePrefixState) :
    intRowStructuredEncodedType.inputSize (prefixRowRunner (n, q)) ≤ n * 6 := by
  rw [prefixRowRunner_eq_prefixRow]
  have hInput := prefixRow_entries_inputSize_le n q
  have hRow := intRowStructured_inputSize_le_length_mul_six hInput
  simpa [prefixRow_length] using hRow

theorem clauseConstraintFromInput_inputSize_le (p : ClauseConstraintInput) :
    constraintStructuredEncodedType.inputSize (clauseConstraintFromInput p) ≤ p.1 * 6 + 6 := by
  rcases p with ⟨n, c⟩
  have hRow := prefixRowRunner_inputSize_le n (clausePrefixFromClause c)
  have hBound := prefixBound_inputSize_le_five (clausePrefixFromClause c)
  simp [clauseConstraintFromInput, constraintStructuredEncodedType]
  omega

end ZeroOneIP
end Karp21
end ComplexityReduction
