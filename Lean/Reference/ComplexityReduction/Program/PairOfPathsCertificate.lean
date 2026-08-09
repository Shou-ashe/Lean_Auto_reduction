/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Program.PairOfPaths
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatListSplitTM
import Mathlib.Tactic

/-!
Reusable flat unary-nat-list encoding for a pair of edge-index paths.

For an edge count `m`, each fixed block has `m + 1` entries.  Its first entry
is the actual path length; the remaining `m` entries contain the path followed
by padding.  Two blocks concatenate into one canonical finite witness.
-/

namespace ComplexityReduction
namespace Program
namespace PairOfPathsCertificate

open ComplexityReduction
open ComplexityReduction.Combinatorics
open ComplexityReduction.Karp21

abbrev natListEncodedType : EncodedType := setStructuredEncodedType

abbrev pathPairEncodedType : EncodedType :=
  EncodedType.prod natListEncodedType natListEncodedType

/-- Decode one fixed path block. -/
def parsePathBlock (block : List Nat) : List Nat :=
  let length := block.getD 0 0
  let body := (NatListSplit.split (1, block)).2
  (NatListSplit.split (length, body)).1

theorem parsePathBlock_tmPolyTime :
    TMPolyTimeMap natListEncodedType natListEncodedType parsePathBlock := by
  let X := natListEncodedType
  have block : TMPolyTimeMap X natListEncodedType id :=
    TMPolyTimeMap.id X
  have zero : TMPolyTimeMap X EncodedType.nat
      (fun _block : List Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have headerInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun block : List Nat => (block, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk block zero
  have header : TMPolyTimeMap X EncodedType.nat
      (fun block : List Nat => block.getD 0 0) := by
    have composed := TMPolyTimeMap.comp
      (EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat)) headerInput
    simpa [Function.comp, X, natListEncodedType, setStructuredEncodedType,
      EncodedListLookup.getD] using composed
  have one : TMPolyTimeMap X EncodedType.nat
      (fun _block : List Nat => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have bodySplitInput : TMPolyTimeMap X NatListSplit.inputEncodedType
      (fun block : List Nat => ((1 : Nat), block)) := by
    simpa [NatListSplit.inputEncodedType, natListEncodedType,
      setStructuredEncodedType, EncodedListLookup.inputEncodedType] using
        TMPolyTimeMap.prod_mk one block
  have bodySplit : TMPolyTimeMap X NatListSplit.outputEncodedType
      (fun block : List Nat => NatListSplit.split (1, block)) := by
    have composed := TMPolyTimeMap.comp NatListSplit.split_tm_polytime bodySplitInput
    simpa [Function.comp] using composed
  have body : TMPolyTimeMap X natListEncodedType
      (fun block : List Nat => (NatListSplit.split (1, block)).2) := by
    have projected := TMPolyTimeMap.snd natListEncodedType natListEncodedType
    have composed := TMPolyTimeMap.comp projected bodySplit
    simpa [Function.comp, NatListSplit.outputEncodedType] using composed
  have pathSplitInput : TMPolyTimeMap X NatListSplit.inputEncodedType
      (fun block : List Nat =>
        (block.getD 0 0, (NatListSplit.split (1, block)).2)) := by
    simpa [NatListSplit.inputEncodedType, natListEncodedType,
      setStructuredEncodedType, EncodedListLookup.inputEncodedType] using
        TMPolyTimeMap.prod_mk header body
  have pathSplit : TMPolyTimeMap X NatListSplit.outputEncodedType
      (fun block : List Nat =>
        NatListSplit.split
          (block.getD 0 0, (NatListSplit.split (1, block)).2)) := by
    have composed := TMPolyTimeMap.comp NatListSplit.split_tm_polytime pathSplitInput
    simpa [Function.comp] using composed
  have first := TMPolyTimeMap.fst natListEncodedType natListEncodedType
  have composed := TMPolyTimeMap.comp first pathSplit
  simpa [Function.comp, parsePathBlock, NatListSplit.outputEncodedType, X] using composed

/-- Split a flat certificate into two fixed blocks and decode both paths. -/
def parsePathPair (input : Nat × List Nat) : List Nat × List Nat :=
  let blocks := NatListSplit.split (input.1 + 1, input.2)
  (parsePathBlock blocks.1, parsePathBlock blocks.2)

theorem parsePathPair_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat natListEncodedType)
      pathPairEncodedType parsePathPair := by
  let X := EncodedType.prod EncodedType.nat natListEncodedType
  have edgeCount : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × List Nat => input.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat natListEncodedType
  have certificate : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat => input.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat natListEncodedType
  have blockSize : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × List Nat => input.1 + 1) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime edgeCount
    simpa [Function.comp, Nat.succ_eq_add_one] using composed
  have splitInput : TMPolyTimeMap X NatListSplit.inputEncodedType
      (fun input : Nat × List Nat => (input.1 + 1, input.2)) := by
    simpa [NatListSplit.inputEncodedType, natListEncodedType,
      setStructuredEncodedType, EncodedListLookup.inputEncodedType] using
        TMPolyTimeMap.prod_mk blockSize certificate
  have blocks : TMPolyTimeMap X NatListSplit.outputEncodedType
      (fun input : Nat × List Nat => NatListSplit.split (input.1 + 1, input.2)) := by
    have composed := TMPolyTimeMap.comp NatListSplit.split_tm_polytime splitInput
    simpa [Function.comp] using composed
  have leftBlock : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat =>
        (NatListSplit.split (input.1 + 1, input.2)).1) := by
    have projected := TMPolyTimeMap.fst natListEncodedType natListEncodedType
    have composed := TMPolyTimeMap.comp projected blocks
    simpa [Function.comp, NatListSplit.outputEncodedType] using composed
  have rightBlock : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat =>
        (NatListSplit.split (input.1 + 1, input.2)).2) := by
    have projected := TMPolyTimeMap.snd natListEncodedType natListEncodedType
    have composed := TMPolyTimeMap.comp projected blocks
    simpa [Function.comp, NatListSplit.outputEncodedType] using composed
  have leftPath : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat =>
        parsePathBlock (NatListSplit.split (input.1 + 1, input.2)).1) := by
    have composed := TMPolyTimeMap.comp parsePathBlock_tmPolyTime leftBlock
    simpa [Function.comp] using composed
  have rightPath : TMPolyTimeMap X natListEncodedType
      (fun input : Nat × List Nat =>
        parsePathBlock (NatListSplit.split (input.1 + 1, input.2)).2) := by
    have composed := TMPolyTimeMap.comp parsePathBlock_tmPolyTime rightBlock
    simpa [Function.comp] using composed
  have output := TMPolyTimeMap.prod_mk leftPath rightPath
  simpa [parsePathPair, pathPairEncodedType, X] using output

/-! ### Canonical witnesses -/

/-- Fixed-width block for one path. -/
def pathBlock (edgeCount : Nat) (path : List Nat) : List Nat :=
  path.length :: path ++ List.replicate (edgeCount - path.length) 0

@[simp] theorem pathBlock_length (edgeCount : Nat) (path : List Nat)
    (lengthBound : path.length ≤ edgeCount) :
    (pathBlock edgeCount path).length = edgeCount + 1 := by
  simp [pathBlock, lengthBound]

theorem parsePathBlock_pathBlock (edgeCount : Nat) (path : List Nat)
    (lengthBound : path.length ≤ edgeCount) :
    parsePathBlock (pathBlock edgeCount path) = path := by
  rw [parsePathBlock, NatListSplit.split_eq_splitAt,
    NatListSplit.split_eq_splitAt]
  simp [pathBlock, lengthBound]

/-- Canonical concatenation of two fixed-width path blocks. -/
def certificate (edgeCount : Nat) (left right : List Nat) : List Nat :=
  pathBlock edgeCount left ++ pathBlock edgeCount right

theorem parsePathPair_certificate (edgeCount : Nat) (left right : List Nat)
    (leftBound : left.length ≤ edgeCount)
    (rightBound : right.length ≤ edgeCount) :
    parsePathPair (edgeCount, certificate edgeCount left right) = (left, right) := by
  rw [parsePathPair, NatListSplit.split_eq_splitAt]
  have leftLength := pathBlock_length edgeCount left leftBound
  rw [show edgeCount + 1 = (pathBlock edgeCount left).length by omega]
  simp [certificate, parsePathBlock_pathBlock, leftBound, rightBound]

end PairOfPathsCertificate
end Program
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Program.PairOfPathsCertificate.parsePathBlock_tmPolyTime,
  ComplexityReduction.Program.PairOfPathsCertificate.parsePathPair_tmPolyTime
