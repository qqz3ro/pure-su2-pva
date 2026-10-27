module

public import KhanSL2.DictionaryStatement
public import Mathlib.Algebra.DirectSum.Module

@[expose] public section

/-!
# Assembly of the coefficient homology maps over spin

For fixed coefficient degree `B` and homological degree `p`, take the algebraic
direct sum of the actual finite-spin homology spaces from milestone M2. The
map `psiTotal` is the direct sum of the specified maps `Current.psiK`, hence
it is surjective. Its target is the direct sum of the duals of the source
pieces, rather than the unrestricted dual of their direct sum.

All maps in this file are complex-linear. No polynomial-ring action is
introduced here.
-/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Modules

/-- The actual coefficient homology, assembled as an algebraic sum over spin. -/
abbrev KTotal (B p : ℕ) := ⨁ S : ℤ, Current.K p B S

/-- The restricted graded dual of the source in coefficient degree `B` and
relative homological degree `p`. -/
abbrev sourceDualTotal (B p : ℕ) :=
  ⨁ S : ℤ, Module.Dual ℂ (Source.piece (Current.kDegree p B S))

/-- Assemble the actual maps obtained by transposing `phi` through the dictionary. -/
def psiTotal (B p : ℕ) : KTotal B p →ₗ[ℂ] sourceDualTotal B p :=
  DirectSum.lmap (fun S : ℤ => Current.psiK p B S)

/-- The spin-`S` component is exactly the previously specified map `psiK`. -/
@[simp] theorem psiTotal_apply (B p : ℕ) (x : KTotal B p) (S : ℤ) :
    psiTotal B p x S = Current.psiK p B S (x S) := rfl

/-- The assembled map sends each homogeneous inclusion to its prescribed image. -/
@[simp] theorem psiTotal_lof (B p : ℕ) (S : ℤ) (x : Current.K p B S) :
    psiTotal B p (DirectSum.lof ℂ ℤ (fun T => Current.K p B T) S x) =
      DirectSum.lof ℂ ℤ
        (fun T => Module.Dual ℂ (Source.piece (Current.kDegree p B T)))
        S (Current.psiK p B S x) :=
  DirectSum.lmap_lof (fun T : ℤ => Current.psiK p B T) S x

/-- Component projections intertwine the assembled and homogeneous maps. -/
theorem psiTotal_component (B p : ℕ) (S : ℤ) :
    (DirectSum.component ℂ ℤ
      (fun T => Module.Dual ℂ (Source.piece (Current.kDegree p B T))) S).comp
        (psiTotal B p) =
      (Current.psiK p B S).comp
        (DirectSum.component ℂ ℤ (fun T => Current.K p B T) S) := rfl

/-- Evaluation still uses the actual dictionary and the actual map `phi`. -/
theorem psiTotal_apply_source (B p : ℕ) (x : KTotal B p) (S : ℤ)
    (a : Source.piece (Current.kDegree p B S)) :
    psiTotal B p x S a =
      Current.dictionary p B S (phiPiece (Current.kDegree p B S) a) (x S) :=
  Current.psiK_apply p B S (x S) a

/-- The sum of the proved surjections `psiK` is surjective: every target has
finite spin support, so its finitely many homogeneous preimages can be added. -/
theorem psiTotal_surjective (B p : ℕ) : Function.Surjective (psiTotal B p) :=
  (DirectSum.lmap_surjective (fun S : ℤ => Current.psiK p B S)).2
    (fun S => Current.psiK_surjective p B S)

end KhanSL2.Modules