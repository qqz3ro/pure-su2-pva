module

public import KhanSL2.BGG.PositiveLaplacianBasics
public import KhanSL2.BGG.PositiveBoundaryProducts

@[expose] public section

/-! The concrete CE Laplacian on products of two positive-current generators. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

private abbrev v (i : ℕ) (a : Fin 3) : Cochain := FiniteExterior.generator (⟨i,a⟩ : Mode)

private def cross (a b : Fin 3) (r s j : ℕ) : Cochain :=
  v (r+j+1) a * v s b - if a=b then ∑ c : Fin 3, v (r+j+1) c * v s c else 0

private def bracketQuadratic (a : Fin 3) (r s : ℕ) : Cochain :=
  ∑ c : Fin 3, ∑ e : Fin 3, epsilon a c e • (v r c * v s e)

private theorem weighted_boundary_triple (a b : Fin 3) (r s j : ℕ) :
    boundary (bracketQuadratic a r s * v j b) =
      boundary (bracketQuadratic a r s) * v j b + cross a b r s j + cross a b s r j := by
  fin_cases a <;> fin_cases b <;>
    simp [bracketQuadratic, cross, v, Fin.sum_univ_succ, epsilon, Finset.sum_mul,
      boundary_triple, boundary_pair, mergeMode, add_mul, sub_mul, neg_mul, smul_mul_assoc] <;> module

private theorem sum_reflect_cross (a b : Fin 3) (i j : ℕ) :
    (∑ r ∈ Finset.range i, cross a b (i-1-r) r j) =
      ∑ r ∈ Finset.range i, cross a b r (i-1-r) j := by
  have h := Finset.sum_range_reflect (fun r => cross a b r (i-1-r) j) i
  apply Eq.trans _ h
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  congr 1
  omega

private theorem boundary_d_mul_generator (i j : ℕ) (a b : Fin 3) :
    boundary (d (v i a) * v j b) =
      (i : ℂ) • (v i a * v j b) - ∑ r ∈ Finset.range i, cross a b r (i-1-r) j := by
  have hd : d (v i a) = -(1/2:ℂ) • ∑ r ∈ Finset.range i,
      bracketQuadratic a r (i-1-r) := d_generator _
  have hb : boundary (d (v i a)) = (i:ℂ) • v i a := by
    simpa only [laplacian_apply, boundary_generator, map_zero, zero_add] using
      laplacian_generator (⟨i,a⟩ : Mode)
  have hcalc : boundary (d (v i a) * v j b) =
      boundary (d (v i a)) * v j b - ∑ r ∈ Finset.range i, cross a b r (i-1-r) j := by
    rw [hd]
    simp only [smul_mul_assoc, Finset.sum_mul, map_smul, map_sum,
      weighted_boundary_triple, Finset.sum_add_distrib]
    rw [sum_reflect_cross]
    module
  rw [hcalc, hb, smul_mul_assoc]

private theorem v_anticomm (i j : ℕ) (a b : Fin 3) : v i a * v j b = -(v j b * v i a) := by
  have h := wedge_generator_supercomm Mode.code Mode.code_injective (⟨i,a⟩ : Mode)
    (FiniteExterior.generator (⟨j,b⟩ : Mode))
  rw [parity_generator] at h
  change v i a * v j b = (-v j b) * v i a at h
  simpa only [neg_mul] using h

private theorem epsilon_quadratic (a b : Fin 3) (r s : ℕ) :
    (∑ k : Fin 3, epsilon k a b • bracketQuadratic k r s) =
      v r a * v s b - v r b * v s a := by
  fin_cases a <;> fin_cases b <;>
    simp [bracketQuadratic, Fin.sum_univ_succ, epsilon] <;> module

private theorem convolution_skew (a b : Fin 3) (N : ℕ) :
    (∑ r ∈ Finset.range (N+1), v r b * v (N-r) a) =
      -(∑ r ∈ Finset.range (N+1), v r a * v (N-r) b) := by
  rw [← Finset.sum_range_reflect (fun r => v r b * v (N-r) a) (N+1)]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  have h : N-(N-r)=r := by omega
  simp only [Nat.add_sub_cancel, h]
  exact v_anticomm _ _ _ _

private theorem d_boundary_pair (i j : ℕ) (a b : Fin 3) :
    d (boundary (v i a * v j b)) =
      ∑ r ∈ Finset.range (i+j+1), v r a * v (i+j-r) b := by
  have hd (k : Fin 3) : d (v (i+j+1) k) =
      -(1/2:ℂ) • ∑ r ∈ Finset.range (i+j+1), bracketQuadratic k r (i+j-r) := by
    simpa only [Nat.add_sub_cancel, bracketQuadratic] using d_generator (⟨i+j+1,k⟩ : Mode)
  have hb : boundary (v i a * v j b) =
      -(∑ k : Fin 3, epsilon k a b • v (i+j+1) k) := boundary_pair _ _
  rw [hb]
  simp only [map_neg, map_sum, map_smul, hd, smul_smul, mul_neg, neg_smul,
    Finset.sum_neg_distrib, neg_neg]
  simp only [smul_neg, Finset.sum_neg_distrib, neg_neg, smul_smul]
  simp_rw [mul_comm (epsilon _ a b) (1/2:ℂ), ← smul_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum, epsilon_quadratic]
  rw [Finset.sum_sub_distrib, convolution_skew]
  module

private theorem sum_split_at {M : Type*} [AddCommMonoid M] (f : ℕ → M) (i j : ℕ) :
    (∑ r ∈ Finset.range (i+j+1), f r) =
      (∑ r ∈ Finset.range j, f r) + f j + ∑ r ∈ Finset.range i, f (j+1+r) := by
  have he : i+j+1=(j+1)+i := by omega
  rw [he, Finset.sum_range_add, Finset.sum_range_succ]
private def pairF (a b : Fin 3) (r s : ℕ) : Cochain :=
  v r a * v s b - if a=b then ∑ c : Fin 3, v r c * v s c else 0

private theorem pairF_skew (a b : Fin 3) (r s : ℕ) :
    pairF b a r s = -pairF a b s r := by
  simp only [pairF, v_anticomm r s]
  by_cases h : a=b
  · subst b
    simp only [ite_true, Finset.sum_neg_distrib]
    abel
  · simp only [if_neg h, if_neg (Ne.symm h), sub_zero]

private theorem pairF_convolution (a b : Fin 3) (N : ℕ) :
    (∑ r ∈ Finset.range (N+1), pairF a b r (N-r)) =
      ∑ r ∈ Finset.range (N+1), v r a * v (N-r) b := by
  have hzero (c : Fin 3) : (∑ r ∈ Finset.range (N+1), v r c * v (N-r) c) = 0 := by
    have h := convolution_skew c c N
    have htwo : (2:ℂ) • (∑ r ∈ Finset.range (N+1), v r c * v (N-r) c) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  simp only [pairF, Finset.sum_sub_distrib]
  split_ifs <;> try simp only [Finset.sum_const_zero, sub_zero]
  rw [Finset.sum_comm]
  simp only [hzero, Finset.sum_const_zero, sub_zero]

private theorem convolution_split {M : Type*} [AddCommGroup M]
    (F : ℕ → ℕ → M) (i j : ℕ) :
    (∑ r ∈ Finset.range i, F (r+j+1) (i-1-r)) +
      (∑ r ∈ Finset.range j, F (j-1-r) (i+r+1)) =
      (∑ r ∈ Finset.range (i+j+1), F r (i+j-r)) - F j i := by
  have hfirst : (∑ r ∈ Finset.range i, F (r+j+1) (i-1-r)) =
      ∑ r ∈ Finset.range i, F (j+1+r) (i+j-(j+1+r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    congr 1 <;> omega
  have hsecond : (∑ r ∈ Finset.range j, F (j-1-r) (i+r+1)) =
      ∑ r ∈ Finset.range j, F r (i+j-r) := by
    rw [← Finset.sum_range_reflect (fun r => F r (i+j-r)) j]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_range.mp hr
    congr 1
    omega
  rw [hfirst, hsecond, sum_split_at]
  have hji : i+j-j=i := by omega
  rw [hji]
  abel

private theorem cross_sum_difference (a b : Fin 3) (i j : ℕ) :
    (∑ r ∈ Finset.range i, cross a b r (i-1-r) j) -
      (∑ r ∈ Finset.range j, cross b a r (j-1-r) i) =
      (∑ r ∈ Finset.range (i+j+1), v r a * v (i+j-r) b) - pairF a b j i := by
  change (∑ r ∈ Finset.range i, pairF a b (r+j+1) (i-1-r)) -
      (∑ r ∈ Finset.range j, pairF b a (r+i+1) (j-1-r)) = _
  simp_rw [pairF_skew a b]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  have hadd (r : ℕ) : r+i+1=i+r+1 := by omega
  simp_rw [hadd]
  rw [convolution_split, pairF_convolution]

private theorem generator_mul_d (i j : ℕ) (a b : Fin 3) :
    v i a * d (v j b) = d (v j b) * v i a := by
  have hp : parityLinear (d (v j b)) = d (v j b) := by
    have h := d_parity (v j b)
    simp only [parity_generator, map_neg] at h
    exact (neg_injective h).symm
  exact wedge_comm_of_parity_even Mode.code Mode.code_injective _ hp _

/-- The CE Laplacian on a generator pair, including the exact color contraction. -/
theorem laplacian_pair (m n : Mode) :
    laplacian (FiniteExterior.generator m * FiniteExterior.generator n) =
      ((m.index+n.index : ℕ):ℂ) • (FiniteExterior.generator m * FiniteExterior.generator n) +
      (if m.color=n.color then ∑ c : Fin 3,
        FiniteExterior.generator (⟨m.index,c⟩ : Mode) *
        FiniteExterior.generator (⟨n.index,c⟩ : Mode) else 0) -
      FiniteExterior.generator (⟨m.index,n.color⟩ : Mode) *
        FiniteExterior.generator (⟨n.index,m.color⟩ : Mode) := by
  obtain ⟨i,a⟩ := m
  obtain ⟨j,b⟩ := n
  change laplacian (v i a * v j b) = _
  rw [laplacian_apply, d_boundary_pair, d_mul]
  simp only [parity_generator, neg_mul, ← sub_eq_add_neg, map_sub]
  rw [generator_mul_d, boundary_d_mul_generator, boundary_d_mul_generator]
  have hant : v j b * v i a = -(v i a * v j b) := v_anticomm _ _ _ _
  rw [hant, smul_neg]
  have hc := cross_sum_difference a b i j
  have hf : pairF a b j i =
      (if a=b then ∑ c : Fin 3, v i c * v j c else 0) - v i b * v j a := by
    simp only [pairF, v_anticomm j i, Finset.sum_neg_distrib]
    split_ifs <;> abel
  change _ = ((i+j:ℕ):ℂ) • (v i a*v j b) + _ - _
  simp only [Nat.cast_add, add_smul]
  calc
    _ = ((i:ℂ) • (v i a*v j b) + (j:ℂ) • (v i a*v j b)) +
        ((∑ r ∈ Finset.range (i+j+1), v r a*v (i+j-r) b) -
         ((∑ r ∈ Finset.range i, cross a b r (i-1-r) j) -
          (∑ r ∈ Finset.range j, cross b a r (j-1-r) i))) := by abel
    _ = _ := by rw [hc, hf]; abel
end KhanSL2.BGG.PositiveCE