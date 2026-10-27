module

public import KhanSL2.Factorization.WeightedRootModelFactorAlgebra
public import KhanSL2.Factorization.WeightedRootModelOrbits
public import KhanSL2.SymmetricFamily.RootBlocks

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

/-- The first odd and even blocks, retaining their respective multiplicities. -/
def firstWeightedSet (q₁ q₂ r₁ r₂ : ℕ) : Finset (Fin (q₁+q₂) ⊕ Fin (r₁+r₂)) :=
  (SymmetricFamily.firstBlock q₁ q₂).val.disjSum (SymmetricFamily.firstBlock r₁ r₂).val

def firstWeightedInclusion (q₁ q₂ r₁ r₂ : ℕ) :
    Fin q₁ ⊕ Fin r₁ → Fin (q₁+q₂) ⊕ Fin (r₁+r₂) :=
  Sum.map (Fin.castAdd q₂) (Fin.castAdd r₂)

def secondWeightedInclusion (q₁ q₂ r₁ r₂ : ℕ) :
    Fin q₂ ⊕ Fin r₂ → Fin (q₁+q₂) ⊕ Fin (r₁+r₂) :=
  Sum.map (Fin.natAdd q₁) (Fin.natAdd r₁)

theorem firstWeightedSet_compl (q₁ q₂ r₁ r₂ : ℕ) :
    (firstWeightedSet q₁ q₂ r₁ r₂)ᶜ =
      (Finset.univ.map (Fin.natAddEmb q₁)).disjSum (Finset.univ.map (Fin.natAddEmb r₁)) := by
  have h : (firstWeightedSet q₁ q₂ r₁ r₂)ᶜ =
      (SymmetricFamily.firstBlock q₁ q₂).valᶜ.disjSum (SymmetricFamily.firstBlock r₁ r₂).valᶜ := by
    ext i
    cases i <;> simp [firstWeightedSet]
  rw [h,SymmetricFamily.firstBlock_compl,SymmetricFamily.firstBlock_compl]

theorem rootProduct_firstWeightedSet {S : Type*} [CommRing S]
    (q₁ q₂ r₁ r₂ : ℕ) (x : Fin (q₁+q₂) ⊕ Fin (r₁+r₂) → S) :
    rootProduct x (rootWeight (q₁+q₂) (r₁+r₂)) (firstWeightedSet q₁ q₂ r₁ r₂) =
      rootProduct (x ∘ firstWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₁ r₁) Finset.univ := by
  simp only [rootProduct,firstWeightedSet,SymmetricFamily.firstBlock,Finset.prod_disjSum,
    Finset.prod_map,Fintype.prod_sum_type,Fin.castAddEmb_apply,firstWeightedInclusion,
    Function.comp_apply,Sum.map_inl,Sum.map_inr,rootWeight,Sum.elim_inl,Sum.elim_inr]

theorem rootProduct_secondWeightedSet {S : Type*} [CommRing S]
    (q₁ q₂ r₁ r₂ : ℕ) (x : Fin (q₁+q₂) ⊕ Fin (r₁+r₂) → S) :
    rootProduct x (rootWeight (q₁+q₂) (r₁+r₂)) (firstWeightedSet q₁ q₂ r₁ r₂)ᶜ =
      rootProduct (x ∘ secondWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₂ r₂) Finset.univ := by
  rw [firstWeightedSet_compl]
  simp only [rootProduct,Finset.prod_disjSum,Finset.prod_map,Fintype.prod_sum_type,
    Fin.natAddEmb_apply,secondWeightedInclusion,Function.comp_apply,Sum.map_inl,Sum.map_inr,
    rootWeight,Sum.elim_inl,Sum.elim_inr]

theorem rootProduct_weightedBlocks {S : Type*} [CommRing S]
    (q₁ q₂ r₁ r₂ : ℕ) (x : Fin (q₁+q₂) ⊕ Fin (r₁+r₂) → S) :
    rootProduct x (rootWeight (q₁+q₂) (r₁+r₂)) Finset.univ =
      rootProduct (x ∘ firstWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₁ r₁) Finset.univ *
      rootProduct (x ∘ secondWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₂ r₂) Finset.univ := by
  simp only [rootProduct,Fintype.prod_sum_type,Fin.prod_univ_add,firstWeightedInclusion,
    secondWeightedInclusion,Function.comp_apply,Sum.map_inl,Sum.map_inr,rootWeight,
    Sum.elim_inl,Sum.elim_inr]
  ring

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]

/-- The actual factor-equation quotient for the specified first odd/even blocks. -/
abbrev BlockFactor (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A) :=
  FactorRing (c.f₁.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
    (c.f₂.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
    (baseRoot (q₁+q₂) (r₁+r₂) A) (rootWeight (q₁+q₂) (r₁+r₂))
    (firstWeightedSet q₁ q₂ r₁ r₂)

def blockRoot (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)
    (i : Fin (q₁+q₂) ⊕ Fin (r₁+r₂)) : BlockFactor c :=
  Ideal.Quotient.mk _ (baseRoot (q₁+q₂) (r₁+r₂) A i)

theorem blockRoot_first_product
    (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A) :
    rootProduct (blockRoot c ∘ firstWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₁ r₁) Finset.univ =
      c.f₁.map (algebraMap A (BlockFactor c)) := by
  have h := ((factorIdeal_le_iff
    (c.f₁.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
    (c.f₂.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
    (baseRoot (q₁+q₂) (r₁+r₂) A) (rootWeight (q₁+q₂) (r₁+r₂))
    (firstWeightedSet q₁ q₂ r₁ r₂) _).mp le_rfl).1
  rw [Polynomial.map_map,Ideal.Quotient.mk_comp_algebraMap,rootProduct_firstWeightedSet] at h
  exact h

theorem blockRoot_second_product
    (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A) :
    rootProduct (blockRoot c ∘ secondWeightedInclusion q₁ q₂ r₁ r₂) (rootWeight q₂ r₂) Finset.univ =
      c.f₂.map (algebraMap A (BlockFactor c)) := by
  have h := ((factorIdeal_le_iff
    (c.f₁.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
    (c.f₂.map (algebraMap A (WeightedBase (q₁+q₂) (r₁+r₂) A)))
    (baseRoot (q₁+q₂) (r₁+r₂) A) (rootWeight (q₁+q₂) (r₁+r₂))
    (firstWeightedSet q₁ q₂ r₁ r₂) _).mp le_rfl).2
  rw [Polynomial.map_map,Ideal.Quotient.mk_comp_algebraMap,rootProduct_secondWeightedSet] at h
  exact h

end KhanSL2.Factorization.WeightedRootModel
