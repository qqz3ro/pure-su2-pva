module

public import KhanSL2.SymmetricFamily.SymmetricBlockWords
public import KhanSL2.SymmetricFamily.BlockStabilizer
public import KhanSL2.SymmetricFamily.RootBlocks

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Literal splitting of labelled words into their first and last blocks,
and compatibility with the actual normalized permutation averages. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
variable {α : Type*}

/-- Restrict an actual ordered word to its two consecutive blocks. -/
def wordBlock (r t : ℕ) : WordSpace α (r+t) →ₗ[ℂ] WordSpace α r ⊗[ℂ] WordSpace α t :=
  Finsupp.linearCombination ℂ (fun u =>
    Finsupp.single (u ∘ Fin.castAdd t) 1 ⊗ₜ[ℂ] Finsupp.single (u ∘ Fin.natAdd r) 1)

@[simp] theorem wordBlock_single (r t : ℕ) (u : Fin (r+t) → α) (c : ℂ) :
    wordBlock r t (Finsupp.single u c) =
      c • (Finsupp.single (u ∘ Fin.castAdd t) 1 ⊗ₜ[ℂ]
        Finsupp.single (u ∘ Fin.natAdd r) 1) :=
  Finsupp.linearCombination_single _ _ _

theorem subsetPolynomial_firstBlock (r t : ℕ) (u : Fin (r+t) → α) :
    subsetPolynomial u (firstBlock r t).val =
      subsetPolynomial (u ∘ Fin.castAdd t) Finset.univ := by
  simp only [subsetPolynomial,firstBlock,Finset.prod_map,Fin.castAddEmb_apply,Function.comp_def]

theorem subsetPolynomial_secondBlock (r t : ℕ) (u : Fin (r+t) → α) :
    subsetPolynomial u (firstBlock r t).valᶜ =
      subsetPolynomial (u ∘ Fin.natAdd r) Finset.univ := by
  rw [firstBlock_compl]
  simp only [subsetPolynomial,Finset.prod_map,Fin.natAddEmb_apply,Function.comp_def]

/-- Multiplication of the two actual word blocks is the previously specified subset map. -/
theorem polynomialBlockWordMap_wordBlock (r t : ℕ) (x : WordSpace α (r+t)) :
    polynomialBlockWordMap (firstBlock r t) x =
      TensorProduct.map (polynomialWordMap r) (polynomialWordMap t) (wordBlock r t x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single u c =>
    simp only [polynomialBlockWordMap_single,wordBlock_single,map_smul,TensorProduct.map_tmul,
      polynomialWordMap_single,one_smul,subsetPolynomial_firstBlock,subsetPolynomial_secondBlock]

/-- Literal block restriction intertwines the actual two independent slot permutations. -/
theorem wordBlock_permute (r t : ℕ) (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin t))
    (x : WordSpace α (r+t)) :
    wordBlock r t (wordPermute (blockPermutationHom r t (σ,τ)) x) =
      TensorProduct.map (wordPermute σ) (wordPermute τ) (wordBlock r t x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single u c =>
    simp only [wordPermute_single,wordBlock_single,map_smul,TensorProduct.map_tmul]
    congr 2 <;> congr 1 <;> funext i <;>
      simp only [Function.comp_apply,blockPermutation_castAdd,blockPermutation_natAdd]

/-- A fully invariant word remains invariant under either permutation of its blocks. -/
theorem wordBlock_fixed (r t : ℕ) (x : WordSpace α (r+t)) (hx : x ∈ invariantWords (r+t))
    (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin t)) :
    TensorProduct.map (wordPermute σ) (wordPermute τ) (wordBlock r t x) = wordBlock r t x := by
  rw [← wordBlock_permute,hx]

/-- Independent normalized block averages preserve the literal split of an invariant word. -/
theorem wordBlock_average (r t : ℕ) (x : WordSpace α (r+t)) (hx : x ∈ invariantWords (r+t)) :
    TensorProduct.map (wordAverage r) (wordAverage t) (wordBlock r t x) = wordBlock r t x := by
  have ha : TensorProduct.map (wordAverage (α:=α) r) (wordAverage (α:=α) t) =
      (Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin r),
      (Fintype.card (Equiv.Perm (Fin t)) : ℂ)⁻¹ • ∑ τ : Equiv.Perm (Fin t),
        TensorProduct.map (wordPermute σ) (wordPermute τ) := by
    change TensorProduct.mapBilinear (RingHom.id ℂ) (WordSpace α r) (WordSpace α t)
      (WordSpace α r) (WordSpace α t) (wordAverage r) (wordAverage t) = _
    simp only [wordAverage,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,
      TensorProduct.mapBilinear_apply]
    simp_rw [← Finset.smul_sum]
    rw [smul_comm,Finset.sum_comm]
  rw [ha]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,wordBlock_fixed r t x hx,
    Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (permutationCard_ne_zero r),one_smul,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (permutationCard_ne_zero t),one_smul]

end KhanSL2.SymmetricFamily
