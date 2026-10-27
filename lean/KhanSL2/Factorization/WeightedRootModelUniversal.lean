module

public import KhanSL2.Factorization.WeightedRootModelBaseChange

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

/-- Universal weighted-root evaluation, retaining the original elementary coefficient map. -/
def rootEvaluation (q r : ℕ) {S : Type*} [CommRing S] [Algebra (Depth.RB (q+2*r)) S]
    (x : Fin q ⊕ Fin r → S)
    (hx : (Collision.univPoly (q+2*r)).map (algebraMap (Depth.RB (q+2*r)) S) =
      rootProduct x (rootWeight q r) Finset.univ) :
    LabelledWeightedRing q r →ₐ[Depth.RB (q+2*r)] S where
  toRingHom := MvPolynomial.eval₂Hom ((algebraMap (Depth.RB (q+2*r)) S).comp MvPolynomial.C) x
  commutes' a := by
    let ev : LabelledWeightedRing q r →+* S := MvPolynomial.eval₂Hom ((algebraMap (Depth.RB (q+2*r)) S).comp MvPolynomial.C) x
    have h : ev.comp (weightedRootMap q r).toRingHom = algebraMap (Depth.RB (q+2*r)) S := by
      apply Collision.CoordSplit.ringHom_eq_of_univPoly
      · rw [← Polynomial.map_map,univPoly_map_weightedRootMap]
        apply Eq.trans _ hx.symm
        have hX (i : Fin q ⊕ Fin r) : ev (show LabelledWeightedRing q r from MvPolynomial.X i) = x i :=
          MvPolynomial.eval₂Hom_X' _ _ _
        have hC (i : Fin q ⊕ Fin r) : (Polynomial.C (show LabelledWeightedRing q r from MvPolynomial.X i)).map ev = Polynomial.C (x i) := by
          rw [Polynomial.map_C,hX]
        simp only [weightedCharacteristic,Polynomial.map_mul,Polynomial.map_prod,
          Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,hC,Polynomial.map_C,hX,
          rootProduct,Fintype.prod_sum_type,rootWeight,Sum.elim_inl,Sum.elim_inr,pow_one]
      · intro z
        change ev (weightedRootMap q r (MvPolynomial.C z)) = _
        rw [show weightedRootMap q r (MvPolynomial.C z) =
          (show LabelledWeightedRing q r from MvPolynomial.C z) from (weightedRootMap q r).commutes z]
        exact MvPolynomial.eval₂Hom_C _ _ _
    exact congrArg (fun f : Depth.RB (q+2*r) →+* S => f a) h

@[simp] theorem rootEvaluation_X (q r : ℕ) {S : Type*} [CommRing S]
    [Algebra (Depth.RB (q+2*r)) S] (x : Fin q ⊕ Fin r → S) (hx) (i : Fin q ⊕ Fin r) :
    rootEvaluation q r x hx (show LabelledWeightedRing q r from MvPolynomial.X i) = x i :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- Weighted root variables determine every map over the prescribed coefficient ring. -/
theorem rootAlgHom_ext (q r : ℕ) {S : Type*} [CommRing S] [Algebra (Depth.RB (q+2*r)) S]
    {f g : LabelledWeightedRing q r →ₐ[Depth.RB (q+2*r)] S}
    (h : ∀ i : Fin q ⊕ Fin r, f (show LabelledWeightedRing q r from MvPolynomial.X i) =
      g (show LabelledWeightedRing q r from MvPolynomial.X i)) : f = g := by
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro z
    have hc : (show LabelledWeightedRing q r from MvPolynomial.C z) =
        algebraMap (Depth.RB (q+2*r)) (LabelledWeightedRing q r) (MvPolynomial.C z) :=
      ((weightedRootMap q r).commutes z).symm
    change f (show LabelledWeightedRing q r from MvPolynomial.C z) =
      g (show LabelledWeightedRing q r from MvPolynomial.C z)
    rw [hc,f.commutes,g.commutes]
  · exact h

variable (q r : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB (q+2*r)) A]

def rootBaseEvaluation {S : Type*} [CommRing S] [Algebra A S]
    [Algebra (Depth.RB (q+2*r)) S] [IsScalarTower (Depth.RB (q+2*r)) A S]
    (x : Fin q ⊕ Fin r → S)
    (hx : (Collision.univPoly (q+2*r)).map (algebraMap (Depth.RB (q+2*r)) S) =
      rootProduct x (rootWeight q r) Finset.univ) :
    WeightedBase q r A →ₐ[A] S :=
  AlgHom.liftEquiv (Depth.RB (q+2*r)) A (LabelledWeightedRing q r) S (rootEvaluation q r x hx)

@[simp] theorem rootBaseEvaluation_baseRoot {S : Type*} [CommRing S] [Algebra A S]
    [Algebra (Depth.RB (q+2*r)) S] [IsScalarTower (Depth.RB (q+2*r)) A S]
    (x : Fin q ⊕ Fin r → S) (hx) (i : Fin q ⊕ Fin r) :
    rootBaseEvaluation q r A x hx (baseRoot q r A i) = x i := by
  change rootBaseEvaluation q r A x hx (1 ⊗ₜ[Depth.RB (q+2*r)]
    (show LabelledWeightedRing q r from MvPolynomial.X i)) = _
  simp [rootBaseEvaluation]

theorem rootBaseAlgHom_ext {S : Type*} [CommRing S] [Algebra A S]
    {f g : WeightedBase q r A →ₐ[A] S}
    (h : ∀ i : Fin q ⊕ Fin r, f (baseRoot q r A i) = g (baseRoot q r A i)) : f = g := by
  let : Algebra (Depth.RB (q+2*r)) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB (q+2*r)) A)).toAlgebra
  let : IsScalarTower (Depth.RB (q+2*r)) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  apply Algebra.TensorProduct.ext_ring
  apply rootAlgHom_ext
  exact h

end KhanSL2.Factorization.WeightedRootModel


