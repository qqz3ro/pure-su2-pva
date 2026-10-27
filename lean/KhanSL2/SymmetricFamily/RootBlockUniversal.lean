module

public import KhanSL2.SymmetricFamily.RootBlocks
public import KhanSL2.SymmetricFamily.RootFactorKernel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Universal property of the actual first-block factor quotient. -/

noncomputable section
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.SymmetricFamily
open Factorization.WeightedRoots

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]

/-- Maps out of the actual first-block quotient are determined on its roots. -/
theorem blockFactorAlgHom_ext (c : Collision.ChartData (r+s) r s A)
    {S : Type*} [CommRing S] [Algebra A S] {f g : BlockFactor c →ₐ[A] S}
    (h : ∀ i, f (blockRoot c i) = g (blockRoot c i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply rootBaseAlgHom_ext
  exact h

/-- Evaluate the actual factor quotient in any ordered pair of root systems. -/
def blockFactorLift (c : Collision.ChartData (r+s) r s A)
    {S : Type*} [CommRing S] [Algebra A S] (x : Fin (r+s) → S)
    (h₁ : ∏ i : Fin r, (Polynomial.X - Polynomial.C (x (Fin.castAdd s i))) =
      c.f₁.map (algebraMap A S))
    (h₂ : ∏ i : Fin s, (Polynomial.X - Polynomial.C (x (Fin.natAdd r i))) =
      c.f₂.map (algebraMap A S)) : BlockFactor c →ₐ[A] S := by
  letI : Algebra (Depth.RB (r+s)) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB (r+s)) A)).toAlgebra
  letI : IsScalarTower (Depth.RB (r+s)) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hx : (Collision.univPoly (r+s)).map (algebraMap (Depth.RB (r+s)) S) =
      ∏ i : Fin (r+s), (Polynomial.X - Polynomial.C (x i)) := by
    rw [IsScalarTower.algebraMap_eq (Depth.RB (r+s)) A S,
      ← Polynomial.map_map, c.factor, Polynomial.map_mul, Fin.prod_univ_add, h₁, h₂]
  let f := rootBaseEvaluation (r+s) A x hx
  have hf : factorIdeal
      (c.f₁.map (algebraMap A (RootBase (r+s) A)))
      (c.f₂.map (algebraMap A (RootBase (r+s) A)))
      (baseRoot (r+s) A) (fun _ => 1) (firstBlock r s).val ≤ RingHom.ker f.toRingHom := by
    apply (factorIdeal_le_ker_iff _ _ _ _ _ _).mpr
    have hc : f.toRingHom.comp (algebraMap A (RootBase (r+s) A)) = algebraMap A S := by
      apply RingHom.ext
      intro a
      exact f.commutes a
    simp only [Polynomial.map_map, hc]
    have he (i : Fin (r+s)) : f.toRingHom (baseRoot (r+s) A i) = x i :=
      rootBaseEvaluation_baseRoot (r+s) A x hx i
    simp only [he, rootProduct, pow_one]
    constructor
    · simpa only [firstBlock, Finset.prod_map, Fin.castAddEmb_apply] using h₁
    · rw [firstBlock_compl]
      simpa only [Finset.prod_map, Fin.natAddEmb_apply] using h₂
  exact Ideal.Quotient.liftₐ _ f (fun a ha => hf ha)

@[simp] theorem blockFactorLift_root (c : Collision.ChartData (r+s) r s A)
    {S : Type*} [CommRing S] [Algebra A S] (x : Fin (r+s) → S) (h₁ h₂) (i : Fin (r+s)) :
    blockFactorLift c x h₁ h₂ (blockRoot c i) = x i := by
  let : Algebra (Depth.RB (r+s)) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB (r+s)) A)).toAlgebra
  let : IsScalarTower (Depth.RB (r+s)) A S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  unfold blockFactorLift blockRoot
  exact rootBaseEvaluation_baseRoot (r+s) A x _ i

end KhanSL2.SymmetricFamily
