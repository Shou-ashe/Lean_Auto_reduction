/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.CodecShape
import ComplexityReduction.Encoding.CodecLayoutIso
import ComplexityReduction.Encoding.LawfulEncodedType
import ComplexityReduction.Encoding.EncoderCoherentView
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

/-!
Minimal production core for lawful V2 representations and presented problems.

This is the only encoding foundation imported by canonical domain hubs.  It
contains structural codec identity, closed structural-presentation evidence,
faithful lawful encodings, exact presented endpoints, and the standard
structural instances.  It deliberately imports neither the optional erased
backend nor Program, Certificate, Protocol, Registry, concrete domain, route,
Legacy, descriptor, packet, provider, or slot APIs.
-/
