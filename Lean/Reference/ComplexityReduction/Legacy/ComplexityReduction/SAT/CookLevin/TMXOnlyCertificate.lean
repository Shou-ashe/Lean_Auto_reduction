/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Enum
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackIOBlocks

/-!
Instance-only certificate surface for the future standard-TM Cook-Levin tableau.

The fixed-run stack block in `TMStackIOBlocks` pins down the whole verifier input
word for one concrete pair `(x, c)`.  The actual root reduction must take only
`x` as input and leave the certificate suffix existential.  This file factors
the fixed input word into the instance prefix and certificate suffix, records the
certificate-size polynomial chosen from `TMVerifier.cert_bound`, and packages the
first x-only semantic boundary without claiming the full tableau theorem.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Chosen certificate bound from a direct TM verifier -/

/-- Degree of the certificate-size polynomial supplied by `TMVerifier.cert_bound`. -/
noncomputable def tmVerifierCertificateBoundDegree {L : EncodedDecisionProblem}
    (V : TMVerifier L) : Nat :=
  Classical.choose V.cert_bound

/-- Coefficient of the certificate-size polynomial supplied by `TMVerifier.cert_bound`. -/
noncomputable def tmVerifierCertificateBoundCoeff {L : EncodedDecisionProblem}
    (V : TMVerifier L) : Nat :=
  Classical.choose (Classical.choose_spec V.cert_bound)

/-- Constant term of the certificate-size polynomial supplied by `TMVerifier.cert_bound`. -/
noncomputable def tmVerifierCertificateBoundConst {L : EncodedDecisionProblem}
    (V : TMVerifier L) : Nat :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec V.cert_bound))

/-- The chosen certificate-size bound as a function of the instance size. -/
noncomputable def tmVerifierCertificateSizeBound {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : Nat :=
  tmVerifierCertificateBoundCoeff V *
      (L.Instance.inputSize x) ^ tmVerifierCertificateBoundDegree V +
    tmVerifierCertificateBoundConst V

/-- The chosen bound still satisfies the verifier's certificate-bound specification. -/
theorem tmVerifierCertificateSizeBound_spec {L : EncodedDecisionProblem}
    (V : TMVerifier L) :
    ∀ x, L.isYes x →
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        V.verify x c = true := by
  simpa [tmVerifierCertificateSizeBound, tmVerifierCertificateBoundDegree,
    tmVerifierCertificateBoundCoeff, tmVerifierCertificateBoundConst] using
      Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec V.cert_bound))

/--
The x-only accepting certificate semantics: a certificate chosen within the
polynomial bound and accepted by the verifier.
-/
structure TMVerifierBoundedAcceptingCertificate {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  verify_true : V.verify x cert = true

namespace TMVerifierBoundedAcceptingCertificate

/-- A bounded accepting certificate gives the normalized accepting run object. -/
noncomputable def acceptedRun {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} (w : TMVerifierBoundedAcceptingCertificate V x) :
    TMVerifierAcceptedRun V x w.cert :=
  TMVerifierAcceptedRun.of_verify_eq_true V x w.cert w.verify_true

/-- Bounded accepting certificates are exactly the `yes` instances of the verifier problem. -/
theorem nonempty_iff_isYes {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) :
    Nonempty (TMVerifierBoundedAcceptingCertificate V x) ↔ L.isYes x := by
  constructor
  · rintro ⟨w⟩
    exact V.sound x w.cert w.verify_true
  · intro hx
    rcases tmVerifierCertificateSizeBound_spec V x hx with
      ⟨c, hSize, hVerify⟩
    exact ⟨{ cert := c, cert_size := hSize, verify_true := hVerify }⟩

end TMVerifierBoundedAcceptingCertificate

/-! ### Factoring the verifier input into an x-prefix and certificate suffix -/

/-- The encoded verifier-input prefix fixed by an instance `x`, including the product delimiter. -/
noncomputable def tmVerifierInstanceInputPrefixEncoded {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) :
    List (tmVerifierInputEncodedType V).Symbol :=
  (L.Instance.encode x).map (fun s => some (Sum.inl s)) ++ [none]

/-- The encoded verifier-input suffix contributed by a concrete certificate. -/
noncomputable def tmVerifierCertificateInputSuffixEncoded {L : EncodedDecisionProblem}
    (V : TMVerifier L) (c : V.Cert.Carrier) :
    List (tmVerifierInputEncodedType V).Symbol :=
  (V.Cert.encode c).map (fun s => some (Sum.inr s))

@[simp]
theorem tmVerifierInstanceInputPrefixEncoded_length {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) :
    (tmVerifierInstanceInputPrefixEncoded V x).length =
      L.Instance.inputSize x + 1 := by
  let xs : List (tmVerifierInputEncodedType V).Symbol :=
    (L.Instance.encode x).map (fun s => some (Sum.inl s))
  change (xs ++ ([none] : List (tmVerifierInputEncodedType V).Symbol)).length =
    L.Instance.inputSize x + 1
  rw [List.length_append]
  simp [xs, EncodedType.inputSize]

@[simp]
theorem tmVerifierCertificateInputSuffixEncoded_length {L : EncodedDecisionProblem}
    (V : TMVerifier L) (c : V.Cert.Carrier) :
    (tmVerifierCertificateInputSuffixEncoded V c).length =
      V.Cert.inputSize c := by
  simp [tmVerifierCertificateInputSuffixEncoded, EncodedType.inputSize]

/-- Product encoding factors into the instance prefix followed by the certificate suffix. -/
theorem tmVerifierInputEncoded_eq_instancePrefix_append_certificateSuffix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    (tmVerifierInputEncodedType V).encode (x, c) =
      tmVerifierInstanceInputPrefixEncoded V x ++
        tmVerifierCertificateInputSuffixEncoded V c := by
  simp only [EncodedType.prod, tmVerifierInstanceInputPrefixEncoded,
    tmVerifierCertificateInputSuffixEncoded]
  rfl

/-- The concrete machine input-stack word prefix fixed by the instance `x`. -/
noncomputable def tmVerifierInstanceInputPrefixWord {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) :
    List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) :=
  (tmVerifierInstanceInputPrefixEncoded V x).map
    (tmVerifierComputableWitness V).inputAlphabet.invFun

/-- The concrete machine input-stack word suffix contributed by a certificate. -/
noncomputable def tmVerifierCertificateInputSuffixWord {L : EncodedDecisionProblem}
    (V : TMVerifier L) (c : V.Cert.Carrier) :
    List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) :=
  (tmVerifierCertificateInputSuffixEncoded V c).map
    (tmVerifierComputableWitness V).inputAlphabet.invFun

@[simp]
theorem tmVerifierInstanceInputPrefixWord_length {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) :
    (tmVerifierInstanceInputPrefixWord V x).length =
      L.Instance.inputSize x + 1 := by
  simp [tmVerifierInstanceInputPrefixWord]

@[simp]
theorem tmVerifierCertificateInputSuffixWord_length {L : EncodedDecisionProblem}
    (V : TMVerifier L) (c : V.Cert.Carrier) :
    (tmVerifierCertificateInputSuffixWord V c).length =
      V.Cert.inputSize c := by
  simp [tmVerifierCertificateInputSuffixWord]

/-- The concrete verifier input word factors into the x-prefix and certificate suffix. -/
theorem tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    tmVerifierInputWord V (x, c) =
      tmVerifierInstanceInputPrefixWord V x ++
        tmVerifierCertificateInputSuffixWord V c := by
  simp [tmVerifierInputWord, tmVerifierInputEncoded_eq_instancePrefix_append_certificateSuffix,
    tmVerifierInstanceInputPrefixWord, tmVerifierCertificateInputSuffixWord, List.map_append]

@[simp]
theorem tmVerifierInputWord_length {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    (tmVerifierInputWord V (x, c)).length =
      L.Instance.inputSize x + 1 + V.Cert.inputSize c := by
  rw [tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix]
  simp [Nat.add_assoc]

/-- Input length bound obtained by allowing any certificate within the chosen size bound. -/
noncomputable def tmVerifierXOnlyInputLengthBound {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : Nat :=
  L.Instance.inputSize x + 1 + tmVerifierCertificateSizeBound V x

theorem tmVerifierXOnlyInputLengthBound_eq_prefix_add_certBound
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier) :
    tmVerifierXOnlyInputLengthBound V x =
      (tmVerifierInstanceInputPrefixWord V x).length +
        tmVerifierCertificateSizeBound V x := by
  simp [tmVerifierXOnlyInputLengthBound, Nat.add_assoc]

theorem tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    (tmVerifierInputWord V (x, c)).length ≤
      tmVerifierXOnlyInputLengthBound V x := by
  rw [tmVerifierInputWord_length, tmVerifierXOnlyInputLengthBound]
  omega

/-- Certificate cells in the x-only surface are the suffix cells allowed by the size bound. -/
def tmVerifierXOnlyCertificateCellWindow {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (cell : Nat) : Prop :=
  (tmVerifierInstanceInputPrefixWord V x).length ≤ cell ∧
    cell < (tmVerifierInstanceInputPrefixWord V x).length +
      tmVerifierCertificateSizeBound V x

theorem tmVerifierCertificateSuffixCell_mem_xOnlyWindow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {i : Nat} (hi : i < (tmVerifierCertificateInputSuffixWord V c).length) :
    tmVerifierXOnlyCertificateCellWindow V x
      ((tmVerifierInstanceInputPrefixWord V x).length + i) := by
  constructor
  · exact Nat.le_add_right _ _
  · have hi' : i < V.Cert.inputSize c := by
      simpa using hi
    have hBound : i < tmVerifierCertificateSizeBound V x :=
      lt_of_lt_of_le hi' hSize
    omega

/-! ### Valid x-only certificate suffixes -/

/--
An encoded suffix is valid for the x-only verifier input when it is exactly the
certificate component of some typed certificate whose encoding length is inside
the chosen certificate bound.
-/
structure TMVerifierEncodedCertificateSuffix {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (suffix : List (tmVerifierInputEncodedType V).Symbol) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  suffix_eq :
    suffix = tmVerifierCertificateInputSuffixEncoded V cert

namespace TMVerifierEncodedCertificateSuffix

/-- The suffix witness reconstructs the typed certificate it came from. -/
def certificate {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List (tmVerifierInputEncodedType V).Symbol}
    (w : TMVerifierEncodedCertificateSuffix V x suffix) : V.Cert.Carrier :=
  w.cert

/-- Valid encoded suffixes are exactly bounded certificate encodings. -/
theorem nonempty_iff_exists {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (suffix : List (tmVerifierInputEncodedType V).Symbol) :
    Nonempty (TMVerifierEncodedCertificateSuffix V x suffix) ↔
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        suffix = tmVerifierCertificateInputSuffixEncoded V c := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.cert, w.cert_size, w.suffix_eq⟩
  · rintro ⟨c, hSize, hSuffix⟩
    exact ⟨{ cert := c, cert_size := hSize, suffix_eq := hSuffix }⟩

/-- Every bounded certificate gives a valid encoded suffix. -/
def ofCertificate {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    TMVerifierEncodedCertificateSuffix V x
      (tmVerifierCertificateInputSuffixEncoded V c) where
  cert := c
  cert_size := hSize
  suffix_eq := rfl

@[simp]
theorem length_eq_cert_size {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List (tmVerifierInputEncodedType V).Symbol}
    (w : TMVerifierEncodedCertificateSuffix V x suffix) :
    suffix.length = V.Cert.inputSize w.cert := by
  cases w with
  | mk cert _ hSuffix =>
      subst suffix
      simp

theorem length_le_bound {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List (tmVerifierInputEncodedType V).Symbol}
    (w : TMVerifierEncodedCertificateSuffix V x suffix) :
    suffix.length ≤ tmVerifierCertificateSizeBound V x := by
  rw [w.length_eq_cert_size]
  exact w.cert_size

/-- A valid encoded suffix completes the x-prefix to the product encoding of its certificate. -/
theorem prefix_append_suffix_eq_inputEncoded {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier}
    {suffix : List (tmVerifierInputEncodedType V).Symbol}
    (w : TMVerifierEncodedCertificateSuffix V x suffix) :
    tmVerifierInstanceInputPrefixEncoded V x ++ suffix =
      (tmVerifierInputEncodedType V).encode (x, w.cert) := by
  cases w with
  | mk cert _ hSuffix =>
      subst suffix
      exact (tmVerifierInputEncoded_eq_instancePrefix_append_certificateSuffix V x cert).symm

end TMVerifierEncodedCertificateSuffix

/--
A machine-word suffix is valid when it is the input-stack word image of a valid
encoded certificate suffix.
-/
structure TMVerifierCertificateWordSuffix {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  suffix_eq :
    suffix = tmVerifierCertificateInputSuffixWord V cert

namespace TMVerifierCertificateWordSuffix

/-- The word-suffix witness reconstructs the typed certificate it came from. -/
def certificate {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix) : V.Cert.Carrier :=
  w.cert

/-- Valid word suffixes are exactly bounded certificate input-stack words. -/
theorem nonempty_iff_exists {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier)
    (suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)) :
    Nonempty (TMVerifierCertificateWordSuffix V x suffix) ↔
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        suffix = tmVerifierCertificateInputSuffixWord V c := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.cert, w.cert_size, w.suffix_eq⟩
  · rintro ⟨c, hSize, hSuffix⟩
    exact ⟨{ cert := c, cert_size := hSize, suffix_eq := hSuffix }⟩

/-- Every bounded certificate gives a valid machine-word suffix. -/
def ofCertificate {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    TMVerifierCertificateWordSuffix V x
      (tmVerifierCertificateInputSuffixWord V c) where
  cert := c
  cert_size := hSize
  suffix_eq := rfl

/-- Mapping a valid encoded suffix through the verifier input alphabet gives a valid word suffix. -/
def ofEncodedSuffix {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List (tmVerifierInputEncodedType V).Symbol}
    (w : TMVerifierEncodedCertificateSuffix V x suffix) :
    TMVerifierCertificateWordSuffix V x
      (suffix.map (tmVerifierComputableWitness V).inputAlphabet.invFun) where
  cert := w.cert
  cert_size := w.cert_size
  suffix_eq := by
    cases w with
    | mk cert _ hSuffix =>
        subst suffix
        rfl

@[simp]
theorem length_eq_cert_size {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix) :
    suffix.length = V.Cert.inputSize w.cert := by
  cases w with
  | mk cert _ hSuffix =>
      subst suffix
      simp

theorem length_le_bound {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix) :
    suffix.length ≤ tmVerifierCertificateSizeBound V x := by
  rw [w.length_eq_cert_size]
  exact w.cert_size

/-- A valid word suffix completes the x-prefix to the concrete verifier input word. -/
theorem prefix_append_suffix_eq_inputWord {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix) :
    tmVerifierInstanceInputPrefixWord V x ++ suffix =
      tmVerifierInputWord V (x, w.cert) := by
  cases w with
  | mk cert _ hSuffix =>
      subst suffix
      exact (tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix V x cert).symm

/-- A valid word suffix keeps the completed input word inside the x-only input bound. -/
theorem prefix_append_suffix_length_le_xOnlyInputLengthBound
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier}
    {suffix : List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀)}
    (w : TMVerifierCertificateWordSuffix V x suffix) :
    (tmVerifierInstanceInputPrefixWord V x ++ suffix).length ≤
      tmVerifierXOnlyInputLengthBound V x := by
  rw [w.prefix_append_suffix_eq_inputWord]
  exact tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le
    V x w.cert w.cert_size

end TMVerifierCertificateWordSuffix

/-! ### x-only initial input-prefix CNF and fixed-run factoring -/

/-- Unit literals fixing only the instance prefix of the verifier input stack. -/
noncomputable def tmVerifierInstanceInputPrefixLiterals {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : List Literal :=
  (tmVerifierInstanceInputPrefixWord V x).zipIdx.map fun entry =>
    tmVerifierInputStackSymbolAtom V 0 entry.2 entry.1

/--
Unit literals for a concrete certificate suffix, indexed after the already fixed
instance prefix.
-/
noncomputable def tmVerifierCertificateInputSuffixLiteralsAt
    {L : EncodedDecisionProblem} (V : TMVerifier L) (start : Nat)
    (c : V.Cert.Carrier) : List Literal :=
  (tmVerifierCertificateInputSuffixWord V c).zipIdx start |>.map fun entry =>
    tmVerifierInputStackSymbolAtom V 0 entry.2 entry.1

/-- x-only initial input block: only the instance prefix is fixed. -/
noncomputable def tmVerifierInstanceInputPrefixCNF {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : CNF :=
  tmVerifierUnitClauses (tmVerifierInstanceInputPrefixLiterals V x)

theorem tmVerifierInstanceInputPrefixCNF_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a ↔
      ∀ l ∈ tmVerifierInstanceInputPrefixLiterals V x, l.eval a = true := by
  simp [tmVerifierInstanceInputPrefixCNF, tmVerifierUnitClauses_satisfies]

/-- The fixed pair input-symbol literals are the x-prefix plus the concrete certificate suffix. -/
theorem tmVerifierInputStackSymbolLiterals_eq_instancePrefix_append_certificateSuffix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    tmVerifierInputStackSymbolLiterals V (x, c) =
      tmVerifierInstanceInputPrefixLiterals V x ++
        tmVerifierCertificateInputSuffixLiteralsAt V
          (tmVerifierInstanceInputPrefixWord V x).length c := by
  rw [tmVerifierInputStackSymbolLiterals,
    tmVerifierInputWord_eq_instancePrefix_append_certificateSuffix,
    tmVerifierInstanceInputPrefixLiterals, tmVerifierCertificateInputSuffixLiteralsAt,
    List.zipIdx_append, List.map_append]
  simp

/-- Any fixed `(x,c)` input-stack block satisfies the x-only instance-prefix block. -/
theorem tmVerifierInputStackInitialCNF_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInputStackInitialCNF V (x, c)) a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a := by
  rw [tmVerifierInstanceInputPrefixCNF_satisfies]
  intro l hl
  have hAll := (tmVerifierInputStackInitialCNF_satisfies V (x, c) a).1 h
  have hSymbol : l ∈ tmVerifierInputStackSymbolLiterals V (x, c) := by
    rw [tmVerifierInputStackSymbolLiterals_eq_instancePrefix_append_certificateSuffix]
    exact List.mem_append_left _ hl
  exact hAll l (List.mem_append_left _ hSymbol)

/-- Any fixed complete initial-stack block satisfies the x-only instance-prefix block. -/
theorem tmVerifierInitialStackCNF_satisfies_instancePrefix
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierInitialStackCNF V (x, c)) a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a := by
  rw [tmVerifierInstanceInputPrefixCNF_satisfies]
  intro l hl
  have hAll := ((tmVerifierInitialStackCNF_satisfies V (x, c) a).1 h).1
  have hSymbol : l ∈ tmVerifierInputStackSymbolLiterals V (x, c) := by
    rw [tmVerifierInputStackSymbolLiterals_eq_instancePrefix_append_certificateSuffix]
    exact List.mem_append_left _ hl
  exact hAll l (List.mem_append_left _ hSymbol)

/-! ### Existential x-only initial seeds -/

/--
An assignment satisfies the x-only existential initial-stack surface when some
bounded certificate makes the old fixed initial-stack block true.
-/
structure TMVerifierXOnlyInitialSeed {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (a : Assignment) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  initial_stack : CNF.Satisfies (tmVerifierInitialStackCNF V (x, cert)) a

namespace TMVerifierXOnlyInitialSeed

theorem nonempty_iff_exists {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment) :
    Nonempty (TMVerifierXOnlyInitialSeed V x a) ↔
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        CNF.Satisfies (tmVerifierInitialStackCNF V (x, c)) a := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.cert, w.cert_size, w.initial_stack⟩
  · rintro ⟨c, hSize, hInit⟩
    exact ⟨{ cert := c, cert_size := hSize, initial_stack := hInit }⟩

/-- Every x-only initial seed satisfies the explicit instance-prefix CNF. -/
theorem prefixCNF_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {a : Assignment}
    (w : TMVerifierXOnlyInitialSeed V x a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  tmVerifierInitialStackCNF_satisfies_instancePrefix V x w.cert a w.initial_stack

end TMVerifierXOnlyInitialSeed

/--
The accepting x-only seed additionally records that the existential certificate
is accepted by the extracted verifier.
-/
structure TMVerifierXOnlyAcceptedSeed {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (a : Assignment) : Type where
  cert : V.Cert.Carrier
  cert_size :
    V.Cert.inputSize cert ≤ tmVerifierCertificateSizeBound V x
  verify_true : V.verify x cert = true
  initial_stack : CNF.Satisfies (tmVerifierInitialStackCNF V (x, cert)) a

namespace TMVerifierXOnlyAcceptedSeed

/-- Forget acceptance and retain only the x-only initial-stack seed. -/
def toInitialSeed {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {a : Assignment}
    (w : TMVerifierXOnlyAcceptedSeed V x a) :
    TMVerifierXOnlyInitialSeed V x a where
  cert := w.cert
  cert_size := w.cert_size
  initial_stack := w.initial_stack

/-- Turn the accepted certificate field into the normalized accepting run object. -/
noncomputable def acceptedRun {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {a : Assignment}
    (w : TMVerifierXOnlyAcceptedSeed V x a) :
    TMVerifierAcceptedRun V x w.cert :=
  TMVerifierAcceptedRun.of_verify_eq_true V x w.cert w.verify_true

theorem nonempty_iff_exists {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (a : Assignment) :
    Nonempty (TMVerifierXOnlyAcceptedSeed V x a) ↔
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        V.verify x c = true ∧
        CNF.Satisfies (tmVerifierInitialStackCNF V (x, c)) a := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.cert, w.cert_size, w.verify_true, w.initial_stack⟩
  · rintro ⟨c, hSize, hVerify, hInit⟩
    exact ⟨{ cert := c, cert_size := hSize, verify_true := hVerify, initial_stack := hInit }⟩

/-- Every accepted x-only seed satisfies the explicit instance-prefix CNF. -/
theorem prefixCNF_satisfies {L : EncodedDecisionProblem} {V : TMVerifier L}
    {x : L.Instance.Carrier} {a : Assignment}
    (w : TMVerifierXOnlyAcceptedSeed V x a) :
    CNF.Satisfies (tmVerifierInstanceInputPrefixCNF V x) a :=
  w.toInitialSeed.prefixCNF_satisfies

end TMVerifierXOnlyAcceptedSeed

end SAT
end ComplexityReduction
