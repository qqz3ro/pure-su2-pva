module

public import KhanSL2.Modules.PowerSumCoordinates
public import KhanSL2.Depth.Collision
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.FiniteType

@[expose] public section

/-! # Labelled-root polynomials over the coefficient ring

The type synonym keeps the elementary-symmetric scalar action distinct from the
ordinary self-action on the same multivariable polynomial ring.
-/

noncomputable section

namespace KhanSL2.PolynomialBGG

open MvPolynomial

/-- Polynomials in the labelled roots, with the coefficient action defined below. -/
def RootPolynomial (B : ℕ) : Type := MvPolynomial (Fin B) ℂ

instance (B : ℕ) : CommRing (RootPolynomial B) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin B) ℂ))

instance (B : ℕ) : Algebra ℂ (RootPolynomial B) :=
  inferInstanceAs (Algebra ℂ (MvPolynomial (Fin B) ℂ))

/-- The coefficient variables are elementary symmetric functions of the roots. -/
def rootMap (B : ℕ) : Depth.RB B →ₐ[ℂ] RootPolynomial B :=
  (symmetricSubalgebra (Fin B) ℂ).val.comp (Modules.elementaryAlgEquiv B).toAlgHom

instance (B : ℕ) : Algebra (Depth.RB B) (RootPolynomial B) :=
  (rootMap B).toRingHom.toAlgebra

@[simp] theorem rootPolynomial_algebraMap (B : ℕ) (r : Depth.RB B) :
    algebraMap (Depth.RB B) (RootPolynomial B) r = rootMap B r := rfl

@[simp] theorem rootMap_apply (B : ℕ) (r : Depth.RB B) :
    rootMap B r = (Modules.elementaryAlgEquiv B r : MvPolynomial (Fin B) ℂ) := rfl

@[simp] theorem rootMap_X (B : ℕ) (i : Fin B) :
    rootMap B (X i) = esymm (Fin B) ℂ (i.val + 1) := by
  change (Modules.elementaryAlgEquiv B (X i) : MvPolynomial (Fin B) ℂ) = _
  rw [Modules.elementaryAlgEquiv_X]

theorem rootPolynomial_smul (B : ℕ) (r : Depth.RB B) (q : RootPolynomial B) :
    r • q = (Modules.elementaryAlgEquiv B r : MvPolynomial (Fin B) ℂ) *
      (show MvPolynomial (Fin B) ℂ from q) := rfl

instance (B : ℕ) : IsScalarTower ℂ (Depth.RB B) (RootPolynomial B) :=
  IsScalarTower.of_algebraMap_eq fun c => ((rootMap B).commutes c).symm

/-- Forget the coefficient action, retaining the ordinary complex polynomial space. -/
def rootPolynomialEquiv (B : ℕ) : RootPolynomial B ≃ₐ[ℂ] MvPolynomial (Fin B) ℂ :=
  AlgEquiv.refl

instance rootPermutationAction (B : ℕ) :
    MulSemiringAction (Equiv.Perm (Fin B)) (RootPolynomial B) where
  smul e p := rename e p
  one_smul p := by exact rename_id_apply p
  mul_smul e f p := by exact (rename_rename f e p).symm
  smul_zero e := map_zero _
  smul_add e p q := map_add _ p q
  smul_one e := map_one _
  smul_mul e p q := map_mul _ p q

@[simp] theorem rootPermutationAction_apply (B : ℕ) (e : Equiv.Perm (Fin B))
    (p : RootPolynomial B) : e • p = rename e (show MvPolynomial (Fin B) ℂ from p) := rfl

instance (B : ℕ) : Algebra.IsInvariant (Depth.RB B) (RootPolynomial B)
    (Equiv.Perm (Fin B)) where
  isInvariant p hp := by
    let q : Modules.R B := ⟨p, hp⟩
    refine ⟨(Modules.elementaryAlgEquiv B).symm q, ?_⟩
    change ((Modules.elementaryAlgEquiv B) ((Modules.elementaryAlgEquiv B).symm q) :
      MvPolynomial (Fin B) ℂ) = p
    rw [AlgEquiv.apply_symm_apply]

/-- The labelled-root algebra is integral over its symmetric coefficients. -/
theorem rootPolynomial_integral (B : ℕ) :
    Algebra.IsIntegral (Depth.RB B) (RootPolynomial B) :=
  Algebra.IsInvariant.isIntegral _ _ (Equiv.Perm (Fin B))

/-- The labelled-root algebra is finite over its symmetric coefficients. -/
theorem rootPolynomial_finite (B : ℕ) :
    Module.Finite (Depth.RB B) (RootPolynomial B) := by
  have : Algebra.FiniteType ℂ (RootPolynomial B) :=
    inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin B) ℂ))
  have : Algebra.FiniteType (Depth.RB B) (RootPolynomial B) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (Depth.RB B) (RootPolynomial B)
  have := rootPolynomial_integral B
  exact Algebra.IsIntegral.finite

instance (B : ℕ) : Module.Finite (Depth.RB B) (RootPolynomial B) := rootPolynomial_finite B

end KhanSL2.PolynomialBGG

