/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.IR.Core.WellFormed

/-!
Basic executable builders over finite relation carriers.
-/

namespace ComplexityReduction

def mkRangeSort (n : Nat) : List ObjId :=
  List.range n

def relTuplesOfSingles (xs : List Nat) : List (List ObjId) :=
  xs.map fun x => [x]

def relTuplesOfPairs (pairs : List (Nat × Nat)) : List (List ObjId) :=
  pairs.map fun p => [p.1, p.2]

def relTuplesOfTriples (triples : List (Nat × (Nat × Nat))) : List (List ObjId) :=
  triples.map fun p => [p.1, p.2.1, p.2.2]

def offsetRelSig (offset : Nat) (sig : RelSig) : RelSig where
  arity := sig.arity.map (fun s => s + offset)

def disjointUnion (U V : UniversalRelIR) : UniversalRelIR where
  sortSizes := U.sortSizes ++ V.sortSizes
  relSigs := U.relSigs ++ V.relSigs.map (offsetRelSig U.numSorts)
  relTuples := U.relTuples ++ V.relTuples

def tagSortBlock (base width tag : Nat) : Nat :=
  base + tag * width

def offsetTuple : List Nat → List Nat → List Nat
  | [], _ => []
  | xs, [] => xs
  | x :: xs, offset :: offsets => (x + offset) :: offsetTuple xs offsets

def offsetTuples (offsets : List Nat) (tuples : List (List Nat)) : List (List Nat) :=
  tuples.map fun tuple => offsetTuple tuple offsets

def relationImage (f : ObjId → ObjId) (tuples : List (List ObjId)) :
    List (List ObjId) :=
  tuples.map fun tuple => tuple.map f

def tupleMap (f : ObjId → ObjId) (tuple : List ObjId) : List ObjId :=
  tuple.map f

def filterTuples (p : List ObjId → Bool) (tuples : List (List ObjId)) :
    List (List ObjId) :=
  tuples.filter p

def projectTuple (indices : List Nat) (tuple : List ObjId) : List ObjId :=
  indices.filterMap fun index => tuple[index]?

def projectArity (indices : List Nat) (arity : List SortId) : List SortId :=
  indices.filterMap fun index => arity[index]?

universe u

@[simp] theorem mem_mkRangeSort_iff {n x : Nat} :
    x ∈ mkRangeSort n ↔ x < n := by
  simp [mkRangeSort]

theorem mkRangeSort_eq_range (n : Nat) :
    mkRangeSort n = List.range n := by
  rfl

@[simp] theorem relTuplesOfSingles_length (xs : List Nat) :
    (relTuplesOfSingles xs).length = xs.length := by
  simp [relTuplesOfSingles]

theorem mem_relTuplesOfSingles_of_mem {xs : List Nat} {x : Nat}
    (h : x ∈ xs) :
    [x] ∈ relTuplesOfSingles xs := by
  exact List.mem_map.mpr ⟨x, h, rfl⟩

theorem mem_relTuplesOfSingles_iff {xs : List Nat} {tuple : List ObjId} :
    tuple ∈ relTuplesOfSingles xs ↔ ∃ x, x ∈ xs ∧ [x] = tuple := by
  simp [relTuplesOfSingles]

theorem relTuplesOfSingles_tupleFamilies_wf
    {sortSize : SortId → Option Nat} {s : SortId} {xs : List Nat}
    (hxs : ∀ x ∈ xs, ∃ n, sortSize s = some n ∧ x < n) :
    ∀ tuple ∈ relTuplesOfSingles xs, TupleFits sortSize [s] tuple := by
  intro tuple hTuple
  rw [relTuplesOfSingles] at hTuple
  rcases List.mem_map.mp hTuple with ⟨x, hx, rfl⟩
  constructor
  · simp
  · intro k s' y hs hy
    cases k with
    | zero =>
        simp at hs hy
        cases hs
        cases hy
        exact hxs x hx
    | succ k =>
        simp at hs

@[simp] theorem relTuplesOfPairs_length (pairs : List (Nat × Nat)) :
    (relTuplesOfPairs pairs).length = pairs.length := by
  simp [relTuplesOfPairs]

theorem mem_relTuplesOfPairs_of_mem {pairs : List (Nat × Nat)} {p : Nat × Nat}
    (h : p ∈ pairs) :
    [p.1, p.2] ∈ relTuplesOfPairs pairs := by
  exact List.mem_map.mpr ⟨p, h, rfl⟩

theorem mem_relTuplesOfPairs_iff {pairs : List (Nat × Nat)} {tuple : List ObjId} :
    tuple ∈ relTuplesOfPairs pairs ↔ ∃ p, p ∈ pairs ∧ [p.1, p.2] = tuple := by
  simp [relTuplesOfPairs]

@[simp] theorem relTuplesOfTriples_length (triples : List (Nat × (Nat × Nat))) :
    (relTuplesOfTriples triples).length = triples.length := by
  simp [relTuplesOfTriples]

theorem mem_relTuplesOfTriples_of_mem
    {triples : List (Nat × (Nat × Nat))} {p : Nat × (Nat × Nat)}
    (h : p ∈ triples) :
    [p.1, p.2.1, p.2.2] ∈ relTuplesOfTriples triples := by
  exact List.mem_map.mpr ⟨p, h, rfl⟩

theorem mem_relTuplesOfTriples_iff
    {triples : List (Nat × (Nat × Nat))} {tuple : List ObjId} :
    tuple ∈ relTuplesOfTriples triples ↔
      ∃ p, p ∈ triples ∧ [p.1, p.2.1, p.2.2] = tuple := by
  simp [relTuplesOfTriples]

theorem relTuplesOfTriples_tupleFamilies_wf
    {sortSize : SortId → Option Nat} {s0 s1 s2 : SortId}
    {triples : List (Nat × (Nat × Nat))}
    (hTriples :
      ∀ p ∈ triples,
        (∃ n, sortSize s0 = some n ∧ p.1 < n) ∧
          (∃ n, sortSize s1 = some n ∧ p.2.1 < n) ∧
            (∃ n, sortSize s2 = some n ∧ p.2.2 < n)) :
    ∀ tuple ∈ relTuplesOfTriples triples,
      TupleFits sortSize [s0, s1, s2] tuple := by
  intro tuple hTuple
  rw [relTuplesOfTriples] at hTuple
  rcases List.mem_map.mp hTuple with ⟨p, hp, rfl⟩
  rcases hTriples p hp with ⟨h0, h1, h2⟩
  constructor
  · simp
  · intro k s x hs hx
    cases k with
    | zero =>
        simp at hs hx
        cases hs
        cases hx
        exact h0
    | succ k =>
        cases k with
        | zero =>
            simp at hs hx
            cases hs
            cases hx
            exact h1
        | succ k =>
            cases k with
            | zero =>
                simp at hs hx
                cases hs
                cases hx
                exact h2
            | succ k =>
                simp at hs

@[simp] theorem relationImage_length (f : ObjId → ObjId) (tuples : List (List ObjId)) :
    (relationImage f tuples).length = tuples.length := by
  simp [relationImage]

@[simp] theorem tupleMap_length (f : ObjId → ObjId) (tuple : List ObjId) :
    (tupleMap f tuple).length = tuple.length := by
  simp [tupleMap]

theorem mem_relationImage_iff {f : ObjId → ObjId} {tuples : List (List ObjId)}
    {tuple' : List ObjId} :
    tuple' ∈ relationImage f tuples ↔ ∃ tuple, tuple ∈ tuples ∧ tuple.map f = tuple' := by
  simp [relationImage]

theorem relationImage_map_length_eq (f : ObjId → ObjId) (tuples : List (List ObjId)) :
    (relationImage f tuples).map List.length = tuples.map List.length := by
  simp [relationImage]

theorem relationImage_tuple_length_of_mem {f : ObjId → ObjId}
    {tuples : List (List ObjId)} {tuple' : List ObjId}
    (h : tuple' ∈ relationImage f tuples) :
    ∃ tuple, tuple ∈ tuples ∧ tuple'.length = tuple.length := by
  rcases mem_relationImage_iff.mp h with ⟨tuple, htuple, rfl⟩
  exact ⟨tuple, htuple, by simp⟩

theorem relationImage_tupleFamilies_wf
    {sourceSortSize targetSortSize : SortId → Option Nat} {arity : List SortId}
    {f : ObjId → ObjId} {tuples : List (List ObjId)}
    (hMap :
      ∀ s x, (∃ n, sourceSortSize s = some n ∧ x < n) →
        ∃ n, targetSortSize s = some n ∧ f x < n)
    (hTuples : ∀ tuple ∈ tuples, TupleFits sourceSortSize arity tuple) :
    ∀ tuple' ∈ relationImage f tuples, TupleFits targetSortSize arity tuple' := by
  intro tuple' hTuple'
  rcases mem_relationImage_iff.mp hTuple' with ⟨tuple, hMem, rfl⟩
  have hTupleFits := hTuples tuple hMem
  constructor
  · simp [hTupleFits.1]
  · intro k s x hs hx
    cases hGet : tuple[k]? with
    | none =>
        simp [List.getElem?_map, hGet] at hx
    | some y =>
        simp [List.getElem?_map, hGet] at hx
        subst x
        exact hMap s y (hTupleFits.2 k s y hs hGet)

theorem filterTuples_length_le (p : List ObjId → Bool) (tuples : List (List ObjId)) :
    (filterTuples p tuples).length ≤ tuples.length := by
  exact List.length_filter_le p tuples

@[simp] theorem mem_filterTuples_iff {p : List ObjId → Bool}
    {tuples : List (List ObjId)} {tuple : List ObjId} :
    tuple ∈ filterTuples p tuples ↔ tuple ∈ tuples ∧ p tuple = true := by
  simp [filterTuples]

theorem filterTuples_tupleFamilies_wf
    {sortSize : SortId → Option Nat} {arity : List SortId}
    {p : List ObjId → Bool} {tuples : List (List ObjId)}
    (hTuples : ∀ tuple ∈ tuples, TupleFits sortSize arity tuple) :
    ∀ tuple ∈ filterTuples p tuples, TupleFits sortSize arity tuple := by
  intro tuple hTuple
  exact hTuples tuple (mem_filterTuples_iff.mp hTuple).1

theorem projectTuple_length_le_indices (indices : List Nat) (tuple : List ObjId) :
    (projectTuple indices tuple).length ≤ indices.length := by
  exact List.length_filterMap_le (fun index => tuple[index]?) indices

@[simp] theorem mem_projectTuple_iff {indices : List Nat} {tuple : List ObjId}
    {value : ObjId} :
    value ∈ projectTuple indices tuple ↔
      ∃ index ∈ indices, tuple[index]? = some value := by
  simp [projectTuple]

theorem projectTuple_length_eq_indices_of_all_lt
    {indices : List Nat} {tuple : List ObjId}
    (hIndices : ∀ index ∈ indices, index < tuple.length) :
    (projectTuple indices tuple).length = indices.length := by
  induction indices with
  | nil =>
      simp [projectTuple]
  | cons index indices ih =>
      have hIndex : index < tuple.length := hIndices index (by simp)
      have hTail : ∀ tailIndex ∈ indices, tailIndex < tuple.length := by
        intro tailIndex hTailIndex
        exact hIndices tailIndex (List.mem_cons_of_mem index hTailIndex)
      cases hGet : tuple[index]? with
      | none =>
          exact False.elim (Nat.not_lt_of_ge (List.getElem?_eq_none_iff.mp hGet) hIndex)
      | some value =>
          have hLen :
              (List.filterMap (fun index => tuple[index]?) indices).length =
                indices.length := by
            simpa [projectTuple] using ih hTail
          simp [projectTuple, hGet, hLen]

theorem projectTuple_tupleFits_projectArity
    {sortSize : SortId → Option Nat} {arity : List SortId}
    {indices : List Nat} {tuple : List ObjId}
    (hTuple : TupleFits sortSize arity tuple) :
    TupleFits sortSize (projectArity indices arity) (projectTuple indices tuple) := by
  induction indices with
  | nil =>
      constructor
      · simp [projectArity, projectTuple]
      · intro k s x hs _
        simp [projectArity] at hs
  | cons index indices ih =>
      have hTail := ih
      cases hArityGet : arity[index]? with
      | none =>
          have hTupleGet : tuple[index]? = none := by
            have hArityBound : arity.length ≤ index :=
              List.getElem?_eq_none_iff.mp hArityGet
            have hTupleBound : tuple.length ≤ index := by
              simpa [hTuple.1] using hArityBound
            exact List.getElem?_eq_none_iff.mpr hTupleBound
          simpa [projectArity, projectTuple, hArityGet, hTupleGet] using hTail
      | some sourceSort =>
          cases hTupleGet : tuple[index]? with
          | none =>
              have hIndex : index < arity.length := by
                rcases List.getElem?_eq_some_iff.mp hArityGet with ⟨hIndex, _⟩
                exact hIndex
              have hTupleBound : tuple.length ≤ index :=
                List.getElem?_eq_none_iff.mp hTupleGet
              exact False.elim
                (Nat.not_lt_of_ge hTupleBound (by simpa [hTuple.1] using hIndex))
          | some value =>
              constructor
              · simpa [projectArity, projectTuple, hArityGet, hTupleGet] using hTail.1
              · intro k s x hs hx
                cases k with
                | zero =>
                    simp [projectArity, projectTuple, hArityGet, hTupleGet] at hs hx
                    subst s
                    subst x
                    exact hTuple.2 index sourceSort value hArityGet hTupleGet
                | succ k =>
                    simp [projectArity, projectTuple, hArityGet, hTupleGet] at hs hx
                    exact hTail.2 k s x hs hx

@[simp] theorem relationTupleFold_nil {α : Type u} (init : α) (step : α → List ObjId → α) :
    List.foldl step init [] = init := by
  rfl

@[simp] theorem relationTupleFold_cons {α : Type u} (init : α) (step : α → List ObjId → α)
    (tuple : List ObjId) (tuples : List (List ObjId)) :
    List.foldl step init (tuple :: tuples) = List.foldl step (step init tuple) tuples := by
  rfl

theorem relationTupleFold_preserves_invariant {α : Type u} {P : α → Prop}
    (init : α) (step : α → List ObjId → α) (tuples : List (List ObjId))
    (hInit : P init) (hStep : ∀ acc tuple, P acc → P (step acc tuple)) :
    P (List.foldl step init tuples) := by
  induction tuples generalizing init with
  | nil =>
      simpa using hInit
  | cons tuple tuples ih =>
      simpa using ih (step init tuple) (hStep init tuple hInit)

theorem relationTupleFold_measure_le_sum_of_step_le {α : Type u}
    (measure : α → Nat) (tupleMeasure : List ObjId → Nat)
    (init : α) (step : α → List ObjId → α) (tuples : List (List ObjId))
    (hStep : ∀ acc tuple, tuple ∈ tuples →
      measure (step acc tuple) ≤ measure acc + tupleMeasure tuple) :
    measure (List.foldl step init tuples) ≤
      measure init + (tuples.map tupleMeasure).sum := by
  induction tuples generalizing init with
  | nil =>
      simp
  | cons tuple tuples ih =>
      have hHead : measure (step init tuple) ≤ measure init + tupleMeasure tuple :=
        hStep init tuple (by simp)
      have hTailStep : ∀ acc tailTuple, tailTuple ∈ tuples →
          measure (step acc tailTuple) ≤ measure acc + tupleMeasure tailTuple := by
        intro acc tailTuple hMem
        exact hStep acc tailTuple (by simp [hMem])
      calc
        measure (List.foldl step init (tuple :: tuples))
            = measure (List.foldl step (step init tuple) tuples) := rfl
        _ ≤ measure (step init tuple) + (tuples.map tupleMeasure).sum :=
          ih (step init tuple) hTailStep
        _ ≤ (measure init + tupleMeasure tuple) + (tuples.map tupleMeasure).sum :=
          Nat.add_le_add_right hHead _
        _ = measure init + ((tuple :: tuples).map tupleMeasure).sum := by
          simp [Nat.add_assoc]

@[simp] theorem offsetTuple_length (offsets tuple : List Nat) :
    (offsetTuple tuple offsets).length = tuple.length := by
  induction tuple generalizing offsets with
  | nil =>
      cases offsets <;> simp [offsetTuple]
  | cons x xs ih =>
      cases offsets with
      | nil => simp [offsetTuple]
      | cons offset offsets => simp [offsetTuple, ih]

@[simp] theorem offsetTuples_length (offsets : List Nat) (tuples : List (List Nat)) :
    (offsetTuples offsets tuples).length = tuples.length := by
  simp [offsetTuples]

theorem mem_offsetTuples_iff {offsets : List Nat} {tuples : List (List Nat)}
    {tuple' : List Nat} :
    tuple' ∈ offsetTuples offsets tuples ↔
      ∃ tuple, tuple ∈ tuples ∧ offsetTuple tuple offsets = tuple' := by
  simp [offsetTuples]

theorem offsetTuples_map_length_eq (offsets : List Nat) (tuples : List (List Nat)) :
    (offsetTuples offsets tuples).map List.length = tuples.map List.length := by
  simp [offsetTuples]

theorem offsetTuple_get?_eq_map_add_getD (offsets tuple : List Nat) (k : Nat) :
    (offsetTuple tuple offsets)[k]? =
      tuple[k]?.map (fun x => x + (offsets[k]?.getD 0)) := by
  induction tuple generalizing offsets k with
  | nil =>
      cases k <;> cases offsets <;> simp [offsetTuple]
  | cons x xs ih =>
      cases k with
      | zero =>
          cases offsets <;> simp [offsetTuple]
      | succ k =>
          cases offsets with
          | nil =>
              simp [offsetTuple, Nat.add_zero]
          | cons offset offsets =>
              simpa [offsetTuple] using ih offsets k

theorem offsetTuples_tupleFamilies_wf
    {sourceSortSize targetSortSize : SortId → Option Nat} {arity : List SortId}
    {offsets : List Nat} {tuples : List (List Nat)}
    (hMap :
      ∀ (k : Nat) (s : SortId) (x : ObjId), arity[k]? = some s →
        (∃ n, sourceSortSize s = some n ∧ x < n) →
          ∃ n, targetSortSize s = some n ∧ x + (offsets[k]?.getD 0) < n)
    (hTuples : ∀ tuple ∈ tuples, TupleFits sourceSortSize arity tuple) :
    ∀ tuple' ∈ offsetTuples offsets tuples, TupleFits targetSortSize arity tuple' := by
  intro tuple' hTuple'
  rcases mem_offsetTuples_iff.mp hTuple' with ⟨tuple, hMem, rfl⟩
  have hTupleFits := hTuples tuple hMem
  constructor
  · simp [hTupleFits.1]
  · intro k s x hs hx
    rw [offsetTuple_get?_eq_map_add_getD offsets tuple k] at hx
    cases hGet : tuple[k]? with
    | none =>
        simp [hGet] at hx
    | some source =>
        simp [hGet] at hx
        subst x
        exact hMap k s source hs (hTupleFits.2 k s source hs hGet)

@[simp] theorem offsetRelSig_arity (offset : Nat) (sig : RelSig) :
    (offsetRelSig offset sig).arity = sig.arity.map (fun s => s + offset) := by
  rfl

@[simp] theorem disjointUnion_sortSizes (U V : UniversalRelIR) :
    (disjointUnion U V).sortSizes = U.sortSizes ++ V.sortSizes := by
  rfl

@[simp] theorem disjointUnion_relSigs (U V : UniversalRelIR) :
    (disjointUnion U V).relSigs = U.relSigs ++ V.relSigs.map (offsetRelSig U.numSorts) := by
  rfl

@[simp] theorem disjointUnion_relTuples (U V : UniversalRelIR) :
    (disjointUnion U V).relTuples = U.relTuples ++ V.relTuples := by
  rfl

@[simp] theorem disjointUnion_numSorts (U V : UniversalRelIR) :
    (disjointUnion U V).numSorts = U.numSorts + V.numSorts := by
  simp [disjointUnion, UniversalRelIR.numSorts]

@[simp] theorem disjointUnion_numRels (U V : UniversalRelIR) :
    (disjointUnion U V).numRels = U.numRels + V.numRels := by
  simp [disjointUnion, UniversalRelIR.numRels]

theorem disjointUnion_left_sortSize?_eq_some
    {U V : UniversalRelIR} {s n : Nat}
    (h : U.sortSize? s = some n) :
    (disjointUnion U V).sortSize? s = some n := by
  unfold UniversalRelIR.sortSize? at h ⊢
  rw [disjointUnion_sortSizes]
  rw [List.getElem?_append_left]
  · exact h
  · rcases List.getElem?_eq_some_iff.mp h with ⟨hs, _⟩
    exact hs

theorem disjointUnion_right_sortSize?_eq_some
    {U V : UniversalRelIR} {s n : Nat}
    (h : V.sortSize? s = some n) :
    (disjointUnion U V).sortSize? (s + U.numSorts) = some n := by
  unfold UniversalRelIR.sortSize? at h ⊢
  rw [disjointUnion_sortSizes]
  rw [Nat.add_comm s U.numSorts]
  rw [List.getElem?_append_right]
  · simpa [UniversalRelIR.numSorts] using h
  · simp [UniversalRelIR.numSorts]

theorem disjointUnion_left_tuple_wf
    {U V : UniversalRelIR} {sig : RelSig} {tuple : List ObjId}
    (hTuple : U.TupleWF sig tuple) :
    (disjointUnion U V).TupleWF sig tuple := by
  constructor
  · exact hTuple.1
  · intro k s x hs hx
    rcases hTuple.2 k s x hs hx with ⟨n, hn, hxlt⟩
    exact ⟨n, disjointUnion_left_sortSize?_eq_some (V := V) hn, hxlt⟩

theorem disjointUnion_right_tuple_wf
    {U V : UniversalRelIR} {sig : RelSig} {tuple : List ObjId}
    (hTuple : V.TupleWF sig tuple) :
    (disjointUnion U V).TupleWF (offsetRelSig U.numSorts sig) tuple := by
  constructor
  · simp [offsetRelSig, hTuple.1]
  · intro k s x hs hx
    unfold offsetRelSig at hs
    rw [List.getElem?_map] at hs
    cases hSigGet : sig.arity[k]? with
    | none =>
        simp [hSigGet] at hs
    | some sourceSort =>
        simp [hSigGet] at hs
        subst s
        rcases hTuple.2 k sourceSort x hSigGet hx with ⟨n, hn, hxlt⟩
        exact ⟨n, disjointUnion_right_sortSize?_eq_some (U := U) hn, hxlt⟩

theorem disjointUnion_wellFormed
    {U V : UniversalRelIR} (hU : U.WellFormed) (hV : V.WellFormed) :
    (disjointUnion U V).WellFormed := by
  constructor
  · simp [disjointUnion, hU.1, hV.1]
  · intro r ts sig hsig htuples t ht
    by_cases hr : r < U.numRels
    · have hsigU : U.relSig? r = some sig := by
        unfold UniversalRelIR.relSig? at hsig ⊢
        rw [disjointUnion_relSigs] at hsig
        rw [List.getElem?_append_left] at hsig
        · exact hsig
        · simpa [UniversalRelIR.numRels] using hr
      have htuplesU : U.tuples? r = some ts := by
        unfold UniversalRelIR.tuples? at htuples ⊢
        rw [disjointUnion_relTuples] at htuples
        rw [List.getElem?_append_left] at htuples
        · exact htuples
        · simpa [UniversalRelIR.numRels, hU.1] using hr
      exact disjointUnion_left_tuple_wf (V := V) (hU.2 r ts sig hsigU htuplesU t ht)
    · have hrRightSig : U.relSigs.length ≤ r := by
        simpa [UniversalRelIR.numRels] using Nat.le_of_not_gt hr
      have hrRightTuples : U.relTuples.length ≤ r := by
        simpa [hU.1] using hrRightSig
      unfold UniversalRelIR.relSig? at hsig
      rw [disjointUnion_relSigs] at hsig
      rw [List.getElem?_append_right hrRightSig] at hsig
      rw [List.getElem?_map] at hsig
      cases hSigGet : V.relSigs[r - U.relSigs.length]? with
      | none =>
          simp [hSigGet] at hsig
      | some sourceSig =>
          simp [hSigGet] at hsig
          subst sig
          have htuplesV : V.tuples? (r - U.relSigs.length) = some ts := by
            unfold UniversalRelIR.tuples? at htuples ⊢
            rw [disjointUnion_relTuples] at htuples
            rw [List.getElem?_append_right hrRightTuples] at htuples
            simpa [hU.1] using htuples
          exact disjointUnion_right_tuple_wf (U := U)
            (hV.2 (r - U.relSigs.length) ts sourceSig hSigGet htuplesV t ht)

/-- Minimal two-sort binary-relation carrier used by view adapters. -/
def binaryRelationIR
    (leftSize rightSize : Nat) (pairs : List (Nat × Nat)) : UniversalRelIR where
  sortSizes := [leftSize, rightSize]
  relSigs := [{ arity := [0, 1] }]
  relTuples := [relTuplesOfPairs pairs]

theorem binaryRelationIR_wellFormed
    {leftSize rightSize : Nat} {pairs : List (Nat × Nat)}
    (hPairs : ∀ p ∈ pairs, p.1 < leftSize ∧ p.2 < rightSize) :
    (binaryRelationIR leftSize rightSize pairs).WellFormed := by
  constructor
  · simp [binaryRelationIR]
  · intro r ts sig hsig htuples t ht
    cases r with
    | zero =>
      simp [binaryRelationIR] at hsig htuples
      cases hsig
      cases htuples
      rw [relTuplesOfPairs] at ht
      rcases List.mem_map.mp ht with ⟨p, hp, rfl⟩
      have hpBounds := hPairs p hp
      constructor
      · simp
      · intro k s x hs hx
        cases k with
        | zero =>
          simp at hs hx
          cases hs
          cases hx
          exact ⟨leftSize, by simp [binaryRelationIR], hpBounds.1⟩
        | succ k =>
          cases k with
          | zero =>
            simp at hs hx
            cases hs
            cases hx
            exact ⟨rightSize, by simp [binaryRelationIR], hpBounds.2⟩
          | succ k =>
            simp at hs
    | succ r =>
      simp [binaryRelationIR] at hsig

end ComplexityReduction
