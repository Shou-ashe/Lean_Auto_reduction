/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedTMSound
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityClasses
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace ComplexityReduction

/--
Machine-readable status tags for the TM2 closure facts needed to interpret the
project-local costed model in direct TM semantics.

These tags are an audit inventory, not proof terms.  Only `available` entries
may be used directly without an additional theorem or witness.
-/
inductive TM2ClosureStatus where
  | available
  | mathlibProofWanted
  | requiresPrimitiveWitness
  | requiresTM2ProgramProof
  | notSoundWithoutGlobalBound
  deriving DecidableEq, Repr

/--
Constructor-level obligations induced by `CostedPolyTimeMap`.  The names mirror
the constructors in `CostedPolyTimeMap` so audit code and documentation can point
to the same obligation surface as the Lean bridge.
-/
inductive CostedTMObligation where
  | ofCosted
  | idMap
  | compMap
  | constMap
  | fstMap
  | sndMap
  | prodMkMap
  | inlMap
  | inrMap
  | listMapMap
  | listAppendMap
  | listFoldlMap
  deriving DecidableEq, Repr

namespace CostedTMObligation

/--
Current local audit status for each costed-to-TM obligation.

`idMap` is available from mathlib's `Turing.idComputableInPolyTime`.
`compMap` is available from the local `seqCompComputableInPolyTime` runner
below, rather than mathlib's still-`proof_wanted`
`Turing.TM2ComputableInPolyTime.comp`.  Sum injections are discharged below by a
concrete prefix-map TM2 program, product projections are discharged by a
concrete filter-map TM2 program, and arbitrary product pairing is discharged by
the local `prodMkComputableInPolyTime` runner.  Arbitrary list-map is discharged
by the local `listMapComputableInPolyTime` runner.  The remaining arbitrary
list-fold closure is not sound from a step witness alone: accumulator encodings
may grow polynomially in the previous accumulator length at each iteration and
therefore exponentially in the source-list length.  A TM bridge for fold needs a
global accumulator/output bound or a restricted constructor.
-/
def tm2Status : CostedTMObligation → TM2ClosureStatus
  | ofCosted => TM2ClosureStatus.requiresPrimitiveWitness
  | idMap => TM2ClosureStatus.available
  | compMap => TM2ClosureStatus.available
  | constMap => TM2ClosureStatus.available
  | fstMap => TM2ClosureStatus.available
  | sndMap => TM2ClosureStatus.available
  | prodMkMap => TM2ClosureStatus.available
  | inlMap => TM2ClosureStatus.available
  | inrMap => TM2ClosureStatus.available
  | listMapMap => TM2ClosureStatus.available
  | listAppendMap => TM2ClosureStatus.available
  | listFoldlMap => TM2ClosureStatus.notSoundWithoutGlobalBound

/-- The full current costed-to-TM obligation inventory. -/
def tm2Inventory : List (CostedTMObligation × TM2ClosureStatus) :=
  [ (ofCosted, tm2Status ofCosted)
  , (idMap, tm2Status idMap)
  , (compMap, tm2Status compMap)
  , (constMap, tm2Status constMap)
  , (fstMap, tm2Status fstMap)
  , (sndMap, tm2Status sndMap)
  , (prodMkMap, tm2Status prodMkMap)
  , (inlMap, tm2Status inlMap)
  , (inrMap, tm2Status inrMap)
  , (listMapMap, tm2Status listMapMap)
  , (listAppendMap, tm2Status listAppendMap)
  , (listFoldlMap, tm2Status listFoldlMap) ]

@[simp] theorem tm2Status_idMap :
    tm2Status idMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_compMap :
    tm2Status compMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_ofCosted :
    tm2Status ofCosted = TM2ClosureStatus.requiresPrimitiveWitness :=
  rfl

@[simp] theorem tm2Status_constMap :
    tm2Status constMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_fstMap :
    tm2Status fstMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_sndMap :
    tm2Status sndMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_prodMkMap :
    tm2Status prodMkMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_inlMap :
    tm2Status inlMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_inrMap :
    tm2Status inrMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_listMapMap :
    tm2Status listMapMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_listAppendMap :
    tm2Status listAppendMap = TM2ClosureStatus.available :=
  rfl

@[simp] theorem tm2Status_listFoldlMap :
    tm2Status listFoldlMap = TM2ClosureStatus.notSoundWithoutGlobalBound :=
  rfl

end CostedTMObligation

/-- The identity costed-to-TM closure obligation discharged by mathlib. -/
theorem costedTM_idMap_from_mathlib {X : EncodedType} : TMPolyTimeMap X X id :=
  TMPolyTimeMap.id X

end ComplexityReduction
