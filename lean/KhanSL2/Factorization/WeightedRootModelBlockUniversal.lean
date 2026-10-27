module

public import KhanSL2.Factorization.WeightedRootModelBlocks
public import KhanSL2.SymmetricFamily.RootFactorKernel

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]

theorem blockFactorAlgHom_ext
    (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)
    {S : Type*} [CommRing S] [Algebra A S] {f g : BlockFactor c →ₐ[A] S}
    (h : ∀ i, f (blockRoot c i) = g (blockRoot c i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply rootBaseAlgHom_ext
  exact h

/-- Evaluate the genuine weighted block quotient in two prescribed root systems. -/
def blockFactorLift
    (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)
    {S : Type*} [CommRing S] [Algebra A S] (x : Fin (q₁+q₂) ⊕ Fin (r₁+r₂) → S)
    (h₁ : rootProduct (x ∘ firstWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₁ r₁) Finset.univ =
      c.f₁.map (algebraMap A S))
    (h₂ : rootProduct (x ∘ secondWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₂ r₂) Finset.univ =
      c.f₂.map (algebraMap A S)) : BlockFactor c →ₐ[A] S := by
  letI : Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A)).toAlgebra
  letI : IsScalarTower (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A S :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hx : (Collision.univPoly ((q₁+q₂)+2*(r₁+r₂))).map
      (algebraMap (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) S) =
      rootProduct x (rootWeight (q₁+q₂) (r₁+r₂)) Finset.univ := by
    rw [IsScalarTower.algebraMap_eq (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A S,
      ← Polynomial.map_map,c.factor,Polynomial.map_mul,rootProduct_weightedBlocks,h₁,h₂]
  let f := rootBaseEvaluation (q₁+q₂) (r₁+r₂) A x hx
  have hf : factorIdeal
      (c.f₁.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
      (c.f₂.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
      (baseRoot (q₁+q₂) (r₁+r₂) A) (rootWeight (q₁+q₂) (r₁+r₂))
      (firstWeightedSet q₁ q₂ r₁ r₂) ≤ RingHom.ker f.toRingHom := by
    apply (SymmetricFamily.factorIdeal_le_ker_iff _ _ _ _ _ _).mpr
    have hc : f.toRingHom.comp (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)) =
        algebraMap A S := by
      apply RingHom.ext
      intro a
      exact f.commutes a
    have he (i : Fin (q₁+q₂) ⊕ Fin (r₁+r₂)) :
        f.toRingHom (baseRoot (q₁+q₂) (r₁+r₂) A i) = x i :=
      rootBaseEvaluation_baseRoot (q₁+q₂) (r₁+r₂) A x hx i
    simp only [Polynomial.map_map,hc,he,rootProduct_firstWeightedSet,rootProduct_secondWeightedSet]
    exact ⟨h₁,h₂⟩
  exact Ideal.Quotient.liftₐ _ f (fun a ha => hf ha)

@[simp] theorem blockFactorLift_root
    (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)
    {S : Type*} [CommRing S] [Algebra A S] (x : Fin (q₁+q₂) ⊕ Fin (r₁+r₂) → S)
    (h₁ h₂) (i : Fin (q₁+q₂) ⊕ Fin (r₁+r₂)) :
    blockFactorLift c x h₁ h₂ (blockRoot c i) = x i := by
  let : Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) S :=
    ((algebraMap A S).comp (algebraMap (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A)).toAlgebra
  let : IsScalarTower (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A S :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  unfold blockFactorLift blockRoot
  exact rootBaseEvaluation_baseRoot (q₁+q₂) (r₁+r₂) A x _ i

end KhanSL2.Factorization.WeightedRootModel
