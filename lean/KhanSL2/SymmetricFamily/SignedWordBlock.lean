module

public import KhanSL2.SymmetricFamily.WordBlock
public import KhanSL2.SymmetricFamily.UncoloredTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The literal word block restriction retains the original independent signs
and normalized antisymmetrization on both blocks. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
variable {α : Type*}

def signedWordPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (WordSpace α k) :=
  (σ.sign : ℂ) • wordPermute σ

def signedWordAverage (k : ℕ) : Module.End ℂ (WordSpace α k) :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • ∑ σ, signedWordPermute σ

/-- Exact tensor coordinates of the already defined signed slot action. -/
theorem polynomialWordBasis_repr_signedSlot {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k (Polynomial ℂ)) :
    (polynomialWordBasis k).repr (signedSlot (Polynomial ℂ) σ x) =
      signedWordPermute σ ((polynomialWordBasis k).repr x) := by
  change (polynomialWordBasis k).repr ((σ.sign : ℂ) • slotPermute (Polynomial ℂ) σ x) = _
  rw [map_smul,polynomialWordBasis_repr_permute]
  rfl

/-- Exact tensor coordinates of the original normalized antisymmetrizer. -/
theorem polynomialWordBasis_repr_signedAverage (k : ℕ) (x : ⨂[ℂ]^k (Polynomial ℂ)) :
    (polynomialWordBasis k).repr (signedAverage (Polynomial ℂ) k x) =
      signedWordAverage k ((polynomialWordBasis k).repr x) := by
  simp only [signedAverage,signedWordAverage,LinearMap.smul_apply,LinearMap.sum_apply,
    map_smul,map_sum,polynomialWordBasis_repr_signedSlot]

/-- Restriction of ordered words retains precisely the product of the two permutation signs. -/
theorem wordBlock_signedPermute (r t : ℕ) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin t))
    (x : WordSpace α (r+t)) :
    wordBlock r t (signedWordPermute (blockPermutationHom r t (σ,τ)) x) =
      TensorProduct.map (signedWordPermute σ) (signedWordPermute τ) (wordBlock r t x) := by
  simp only [signedWordPermute,LinearMap.smul_apply,map_smul,wordBlock_permute,
    TensorProduct.map_smul_left,TensorProduct.map_smul_right,LinearMap.smul_apply,smul_smul]
  congr 1
  simp only [blockPermutation_sign,Units.val_mul,Int.cast_mul]
  exact mul_comm _ _

/-- A signed invariant word is fixed by the independent signed block averages. -/
theorem wordBlock_signedAverage (r t : ℕ) (x : WordSpace α (r+t))
    (hx : ∀ σ, signedWordPermute σ x = x) :
    TensorProduct.map (signedWordAverage r) (signedWordAverage t) (wordBlock r t x) =
      wordBlock r t x := by
  have hfixed (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin t)) :
      TensorProduct.map (signedWordPermute σ) (signedWordPermute τ) (wordBlock r t x) =
        wordBlock r t x := by rw [← wordBlock_signedPermute,hx]
  have ha : TensorProduct.map (signedWordAverage (α:=α) r) (signedWordAverage (α:=α) t) =
      (Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin r),
      (Fintype.card (Equiv.Perm (Fin t)) : ℂ)⁻¹ • ∑ τ : Equiv.Perm (Fin t),
        TensorProduct.map (signedWordPermute σ) (signedWordPermute τ) := by
    change TensorProduct.mapBilinear (RingHom.id ℂ) (WordSpace α r) (WordSpace α t)
      (WordSpace α r) (WordSpace α t) (signedWordAverage r) (signedWordAverage t) = _
    simp only [signedWordAverage,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,
      TensorProduct.mapBilinear_apply]
    simp_rw [← Finset.smul_sum]
    rw [smul_comm,Finset.sum_comm]
  rw [ha]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,hfixed,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (permutationCard_ne_zero r),one_smul,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (permutationCard_ne_zero t),one_smul]

end KhanSL2.SymmetricFamily
