module

public import KhanSL2.CE
public import KhanSL2.SourceData

@[expose] public section

/-!
# Fixed data and the precise structural assertions

The operations on finite cochains and on the source are fixed definitions.
The named predicates in this file are propositions, not assumed instances.
They are proved in `CEComplex` and `TargetPVA` before the main proposition.
-/

noncomputable section

namespace KhanSL2

def cochainData : DifferentialData Cochain where
  one := cochainOne
  mul := wedgeLinear
  translation := translation
  piece := cochainPiece

/-- These are structural assertions about the *defined* CE differential.
The closed theorem `relativeComplex_laws` proves every field. In particular,
these laws certify that the cycle/image quotient is the ordinary cohomology
of the restricted relative CE complex. -/
structure RelativeComplexLaws : Prop where
  square_zero : ∀ u : Cochain, q (q u) = 0
  invariant_preservation : ∀ u ∈ relativeInvariants, q u ∈ relativeInvariants
  one_closed : q cochainOne = 0
  degree : ∀ d u, u ∈ cochainPiece d →
    q u ∈ cochainPiece (d.1 + 1, d.2.1, d.2.2)
  odd_leibniz : ∀ d u v, u ∈ cochainPiece d →
    q (wedge u v) =
      wedge (q u) v + (if d.1 % 2 = 0 then (1 : ℂ) else -1) • wedge u (q v)
  translation_commutes : ∀ u ∈ relativeInvariants,
    q (translation u) = translation (q u)

/-- The normalized `bc` bracket on finite modes.

`Mode.c k b` is the paper's `c_(k+1)^b`; hence its factorial is `(k+1)!`.
The reverse mixed bracket is fixed by super-skew symmetry in `IsPVA`.
These formulas specify the bracket independently of the desired isomorphism.
-/
structure IsBCBracket (br : LambdaBracket Cochain) : Prop where
  bb : ∀ j k a b, br (generator (.b j a)) (generator (.b k b)) = 0
  cc : ∀ j k a b, br (generator (.c j a)) (generator (.c k b)) = 0
  bc : ∀ j k a b,
    br (generator (.b j a)) (generator (.c k b)) =
      Finsupp.single (j + k + 1)
        ((if a = b then
          (-1 : ℂ) ^ j / ((Nat.factorial j : ℂ) * (Nat.factorial (k + 1) : ℂ))
          else 0) • cochainOne)

/-- Every target operation must be induced by the fixed cochain operation.

Existential cycle proofs assert closure, rather than making these conditions
vacuous for an expression that is not a cycle. `grading` fixes the homogeneous
pieces to those represented by homogeneous relative cocycles.
-/
structure IsInducedOnCohomology
    (brC : LambdaBracket Cochain)
    (DH : DifferentialData Cohomology) (brH : LambdaBracket Cohomology) : Prop where
  unit : ∃ h : cochainOne ∈ relativeCycles,
    DH.one = classOf cochainOne h
  product : ∀ u v (hu : u ∈ relativeCycles) (hv : v ∈ relativeCycles),
    ∃ h : wedge u v ∈ relativeCycles,
      DH.mul (classOf u hu) (classOf v hv) = classOf (wedge u v) h
  translation : ∀ u (hu : u ∈ relativeCycles),
    ∃ h : KhanSL2.translation u ∈ relativeCycles,
      DH.translation (classOf u hu) = classOf (KhanSL2.translation u) h
  bracket : ∀ u v (hu : u ∈ relativeCycles) (hv : v ∈ relativeCycles) n,
    ∃ h : brC u v n ∈ relativeCycles,
      brH (classOf u hu) (classOf v hv) n = classOf (brC u v n) h
  grading : ∀ d h, h ∈ DH.piece d ↔ cohomologyHomogeneous d h

end KhanSL2
