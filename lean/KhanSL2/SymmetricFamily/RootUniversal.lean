module

public import KhanSL2.SymmetricFamily.RootBaseChange

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Universal property of the actual labelled-root algebra over its fixed
coefficient ring, including arbitrary coefficient base changes. -/

noncomputable section
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- Evaluate labelled roots while retaining the fixed elementary coefficient map. -/
def rootEvaluation (k : ℕ) {S : Type*} [CommRing S] [Algebra (Depth.RB k) S]
    (x : Fin k → S)
    (hx : (Collision.univPoly k).map (algebraMap (Depth.RB k) S) =
      ∏ i : Fin k, (Polynomial.X - Polynomial.C (x i))) :
    RootPolynomial k →ₐ[Depth.RB k] S where
  toRingHom := MvPolynomial.eval₂Hom ((algebraMap (Depth.RB k) S).comp MvPolynomial.C) x
  commutes' a := by
    have h : (MvPolynomial.eval₂Hom ((algebraMap (Depth.RB k) S).comp MvPolynomial.C) x).comp
        (rootMap k).toRingHom = algebraMap (Depth.RB k) S := by
      apply Collision.CoordSplit.ringHom_eq_of_univPoly
      · rw [← Polynomial.map_map, univPoly_map_rootMap]
        rw [labelledCharacteristic, Polynomial.map_prod]
        apply Eq.trans _ hx.symm
        apply Finset.prod_congr rfl
        intro i _
        change Polynomial.map
          (MvPolynomial.eval₂Hom ((algebraMap (Depth.RB k) S).comp MvPolynomial.C) x)
          ((Polynomial.X : Polynomial (MvPolynomial (Fin k) ℂ)) - Polynomial.C (MvPolynomial.X i)) =
            Polynomial.X - Polynomial.C (x i)
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, MvPolynomial.eval₂Hom_X']
      · intro z
        change MvPolynomial.eval₂Hom ((algebraMap (Depth.RB k) S).comp MvPolynomial.C) x
          (rootMap k (MvPolynomial.C z)) = _
        rw [show rootMap k (MvPolynomial.C z) =
          (show RootPolynomial k from MvPolynomial.C z) from (rootMap k).commutes z]
        exact MvPolynomial.eval₂Hom_C _ _ _
    exact congrArg (fun f : Depth.RB k →+* S => f a) h

@[simp] theorem rootEvaluation_X (k : ℕ) {S : Type*} [CommRing S]
    [Algebra (Depth.RB k) S] (x : Fin k → S) (hx) (i : Fin k) :
    rootEvaluation k x hx (show RootPolynomial k from MvPolynomial.X i) = x i :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Root variables determine an algebra map over the coefficient ring. -/
theorem rootAlgHom_ext (k : ℕ) {S : Type*} [CommRing S] [Algebra (Depth.RB k) S]
    {f g : RootPolynomial k →ₐ[Depth.RB k] S}
    (h : ∀ i : Fin k, f (show RootPolynomial k from MvPolynomial.X i) =
      g (show RootPolynomial k from MvPolynomial.X i)) : f = g := by
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro z
    have hc : (show RootPolynomial k from MvPolynomial.C z) =
        algebraMap (Depth.RB k) (RootPolynomial k) (MvPolynomial.C z) :=
      ((rootMap k).commutes z).symm
    change f (show RootPolynomial k from MvPolynomial.C z) =
      g (show RootPolynomial k from MvPolynomial.C z)
    rw [hc, f.commutes, g.commutes]
  · exact h

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- A specified splitting into labelled roots gives a unique map out of actual root base change. -/
def rootBaseEvaluation {S : Type*} [CommRing S] [Algebra A S]
    [Algebra (Depth.RB k) S] [IsScalarTower (Depth.RB k) A S]
    (x : Fin k → S)
    (hx : (Collision.univPoly k).map (algebraMap (Depth.RB k) S) =
      ∏ i : Fin k, (Polynomial.X - Polynomial.C (x i))) :
    RootBase k A →ₐ[A] S :=
  AlgHom.liftEquiv (Depth.RB k) A (RootPolynomial k) S (rootEvaluation k x hx)

@[simp] theorem rootBaseEvaluation_baseRoot {S : Type*} [CommRing S] [Algebra A S]
    [Algebra (Depth.RB k) S] [IsScalarTower (Depth.RB k) A S]
    (x : Fin k → S) (hx) (i : Fin k) :
    rootBaseEvaluation k A x hx (baseRoot k A i) = x i := by
  change rootBaseEvaluation k A x hx (1 ⊗ₜ[Depth.RB k]
    (show RootPolynomial k from MvPolynomial.X i)) = _
  simp [rootBaseEvaluation]

/-- The coefficient scalars and labelled roots uniquely determine each base-changed map. -/
theorem rootBaseAlgHom_ext {S : Type*} [CommRing S] [Algebra A S]
    {f g : RootBase k A →ₐ[A] S}
    (h : ∀ i : Fin k, f (baseRoot k A i) = g (baseRoot k A i)) : f = g := by
  let : Algebra (Depth.RB k) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB k) A)).toAlgebra
  let : IsScalarTower (Depth.RB k) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply Algebra.TensorProduct.ext_ring
  apply rootAlgHom_ext
  exact h

end KhanSL2.SymmetricFamily
