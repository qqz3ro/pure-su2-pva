module

public import KhanSL2.SymmetricFamily.SymmetricBlockWords

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exact binomial normalization of the actual primitive symmetric coproduct,
with its two actual homogeneous-component projections. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily

variable {α : Type*}

/-- The existing primitive polynomial coproduct followed by the actual degree projections. -/
def polynomialPrimitiveComponent (k r : ℕ) : MvPolynomial α ℂ →ₗ[ℂ]
    MvPolynomial α ℂ ⊗[ℂ] MvPolynomial α ℂ :=
  (TensorProduct.map (MvPolynomial.homogeneousComponent r)
    (MvPolynomial.homogeneousComponent (k-r))).comp polynomialPrimitive.toLinearMap

/-- Homogeneous projection keeps exactly subsets of the prescribed block size. -/
theorem polynomialPrimitiveComponent_word (k r : ℕ) (u : Fin k → α) :
    polynomialPrimitiveComponent k r (subsetPolynomial u Finset.univ) =
      ∑ S : Assignment k r, subsetPolynomial u S.val ⊗ₜ[ℂ] subsetPolynomial u S.valᶜ := by
  change TensorProduct.map (MvPolynomial.homogeneousComponent r)
    (MvPolynomial.homogeneousComponent (k-r))
      (polynomialPrimitive (subsetPolynomial u Finset.univ)) = _
  rw [polynomialPrimitive_word,map_sum]
  have hS (S : Finset (Fin k)) :
      TensorProduct.map (MvPolynomial.homogeneousComponent r)
        (MvPolynomial.homogeneousComponent (k-r))
          (subsetPolynomial u S ⊗ₜ[ℂ] subsetPolynomial u Sᶜ) =
        if S.card=r then subsetPolynomial u S ⊗ₜ[ℂ] subsetPolynomial u Sᶜ else 0 := by
    rw [TensorProduct.map_tmul,
      MvPolynomial.homogeneousComponent_of_mem (subsetPolynomial_mem_degree u S),
      MvPolynomial.homogeneousComponent_of_mem (subsetPolynomial_mem_degree u Sᶜ)]
    by_cases h : S.card=r
    · have hc : k-r=Sᶜ.card := by simp [Finset.card_compl,h]
      rw [if_pos h.symm,if_pos hc,if_pos h]
    · rw [if_neg (Ne.symm h),TensorProduct.zero_tmul,if_neg h]
  simp only [hS]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun S : Finset (Fin k) => S.card=r))
    (by simp) (fun S => subsetPolynomial u S ⊗ₜ[ℂ] subsetPolynomial u Sᶜ)

/-- The actual component on arbitrary finite linear combinations of labelled words. -/
theorem polynomialPrimitiveComponent_wordMap (k r : ℕ) (x : WordSpace α k) :
    polynomialPrimitiveComponent k r (polynomialWordMap k x) =
      ∑ S : Assignment k r, polynomialBlockWordMap S x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy,Finset.sum_add_distrib]
  | single u c =>
    simp only [polynomialWordMap_single,map_smul,polynomialPrimitiveComponent_word,
      polynomialBlockWordMap_single,Finset.smul_sum]

/-- The specified primitive component is choose(k,r) times the original
normalized block map, for arbitrary variables and arbitrary finite input. -/
theorem polynomialPrimitiveComponent_normalized {k r : ℕ}
    (S : Assignment k r) (x : WordSpace α k) :
    polynomialPrimitiveComponent k r (polynomialWordMap k x) =
      (Nat.choose k r : ℂ) • polynomialBlockWordMap S (wordAverage k x) := by
  rw [polynomialPrimitiveComponent_wordMap,polynomialBlockWordMap_average S x]

/-- The identical formula expressed with the verified inverse binomial factor. -/
theorem polynomialBlockWordMap_normalized {k r : ℕ}
    (S : Assignment k r) (x : WordSpace α k) :
    polynomialBlockWordMap S (wordAverage k x) =
      (Nat.choose k r : ℂ)⁻¹ • polynomialPrimitiveComponent k r (polynomialWordMap k x) := by
  rw [polynomialPrimitiveComponent_normalized S x,smul_smul,
    inv_mul_cancel₀ (assignment_choose_ne_zero S),one_smul]

end KhanSL2.SymmetricFamily
