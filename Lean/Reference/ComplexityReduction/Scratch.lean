import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedType

open ComplexityReduction

#check List.get
example (xs : List Nat) (i : Nat) (h : i < xs.length) : Nat := xs[i]'(h)
