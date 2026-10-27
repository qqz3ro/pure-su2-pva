module

public import KhanSL2.Factorization.KunnethTensorModel
public import KhanSL2.Factorization.ShuffleEuler
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Finite homogeneous expansion in both factors of the actual relative tensor. -/

noncomputable section
open scoped TensorProduct DirectSum BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- Both tensor factors retain their actual homogeneous decomposition. -/
def tensorDegreeSumEquiv :
    (⨁ pq : ℕ × ℕ, degree M pq.1 ⊗[ℂ] degree N pq.2) ≃ₗ[ℂ]
      RelativeChains M ⊗[ℂ] RelativeChains N :=
  (TensorProduct.directSum ℂ ℂ (fun p => degree M p) (fun q => degree N q)).symm.trans
    (TensorProduct.congr (degreeSumEquiv M) (degreeSumEquiv N))

@[simp] theorem tensorDegreeSumEquiv_of_tmul (p q : ℕ)
    (u : degree M p) (v : degree N q) :
    tensorDegreeSumEquiv M N
      (DirectSum.lof ℂ (ℕ × ℕ) (fun pq => degree M pq.1 ⊗[ℂ] degree N pq.2)
        (p,q) (u ⊗ₜ[ℂ] v)) = u.val ⊗ₜ[ℂ] v.val := by
  rw [tensorDegreeSumEquiv, LinearEquiv.trans_apply,
    TensorProduct.directSum_symm_lof_tmul, TensorProduct.congr_tmul]
  simp only [DirectSum.lof_eq_of, degreeSumEquiv_of]

/-- Projection onto one exterior bidegree of the actual relative tensor. -/
def tensorBidegreeComponent (p q : ℕ) :
    RelativeChains M ⊗[ℂ] RelativeChains N →ₗ[ℂ] degree M p ⊗[ℂ] degree N q :=
  TensorProduct.map (degreeComponent M p) (degreeComponent N q)

@[simp] theorem tensorBidegreeComponent_tmul (p q : ℕ)
    (u : RelativeChains M) (v : RelativeChains N) :
    tensorBidegreeComponent M N p q (u ⊗ₜ[ℂ] v) =
      degreeComponent M p u ⊗ₜ[ℂ] degreeComponent N q v := rfl

theorem tensorBidegreeComponent_sum (w : ⨁ pq : ℕ × ℕ,
    degree M pq.1 ⊗[ℂ] degree N pq.2) (p q : ℕ) :
    tensorBidegreeComponent M N p q (tensorDegreeSumEquiv M N w) = w (p,q) := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | add w v hw hv =>
    simp only [map_add, hw, hv]
    rfl
  | of pq t =>
    rcases pq with ⟨r,s⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      simp only [map_add, hu, hv]
      rfl
    | tmul u v =>
      rw [← DirectSum.lof_eq_of ℂ, tensorDegreeSumEquiv_of_tmul,
        tensorBidegreeComponent_tmul]
      by_cases hp : p = r
      · subst r
        by_cases hq : q = s
        · subst s
          simp only [degreeComponent_subtype, DirectSum.lof_eq_of, DirectSum.of_eq_same]
        · rw [degreeComponent_subtype_ne N hq, TensorProduct.tmul_zero]
          have hneq : (p,q) ≠ (p,s) := fun h => hq (congrArg Prod.snd h)
          exact (DirectSum.of_eq_of_ne (β := fun pq : ℕ × ℕ => degree M pq.1 ⊗[ℂ] degree N pq.2) (p,s) (p,q) (u ⊗ₜ[ℂ] v) hneq).symm
      · rw [degreeComponent_subtype_ne M hp, TensorProduct.zero_tmul]
        have hneq : (p,q) ≠ (r,s) := fun h => hp (congrArg Prod.fst h)
        exact (DirectSum.of_eq_of_ne (β := fun pq : ℕ × ℕ => degree M pq.1 ⊗[ℂ] degree N pq.2) (r,s) (p,q) (u ⊗ₜ[ℂ] v) hneq).symm

theorem tensorDegreeSumEquiv_symm_apply (z : RelativeChains M ⊗[ℂ] RelativeChains N)
    (p q : ℕ) : (tensorDegreeSumEquiv M N).symm z (p,q) =
      tensorBidegreeComponent M N p q z := by
  rw [← tensorBidegreeComponent_sum M N ((tensorDegreeSumEquiv M N).symm z),
    LinearEquiv.apply_symm_apply]

/-- A relative chain's degree component has the corresponding Euler eigenvalue. -/
theorem degreeComponent_euler (p : ℕ) (z : RelativeChains M) :
    degreeComponent M p (relativeEuler M z) = (p : ℂ) • degreeComponent M p z := by
  obtain ⟨w, rfl⟩ := (degreeSumEquiv M).surjective z
  induction w using DirectSum.induction_on with
  | zero => simp
  | add w v hw hv => simp only [map_add, hw, hv, smul_add]
  | of q u =>
    rw [degreeSumEquiv_of, relativeEuler_of_mem_degree M u.property, map_smul]
    by_cases hpq : p = q
    · subst q
      rfl
    · rw [degreeComponent_subtype_ne M hpq, smul_zero, smul_zero]

/-- Total Euler degree acts diagonally on the actual tensor bidegree components. -/
theorem tensorBidegreeComponent_euler (p q : ℕ)
    (z : RelativeChains M ⊗[ℂ] RelativeChains N) :
    tensorBidegreeComponent M N p q (relativeTensorEuler (M := M) (N := N) z) =
      ((p+q : ℕ) : ℂ) • tensorBidegreeComponent M N p q z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw, smul_add]
  | tmul u v =>
    rw [relativeTensorEuler_tmul, map_add, tensorBidegreeComponent_tmul,
      tensorBidegreeComponent_tmul, tensorBidegreeComponent_tmul,
      degreeComponent_euler, degreeComponent_euler,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, Nat.cast_add, add_smul]
    rw [TensorProduct.add_tmul]
    congr 1

/-- A total-degree eigenvector has no components in a different total degree. -/
theorem tensorBidegreeComponent_eq_zero_of_eigen {n p q : ℕ}
    (hneq : p+q ≠ n) {z : RelativeChains M ⊗[ℂ] RelativeChains N}
    (hz : relativeTensorEuler (M := M) (N := N) z = (n : ℂ) • z) :
    tensorBidegreeComponent M N p q z = 0 := by
  have he := congrArg (tensorBidegreeComponent M N p q) hz
  rw [tensorBidegreeComponent_euler, map_smul] at he
  by_contra hw
  have hcast : ((p+q : ℕ) : ℂ) = (n : ℂ) :=
    smul_left_injective (M := degree M p ⊗[ℂ] degree N q)
      (m := tensorBidegreeComponent M N p q z) ℂ hw he
  exact hneq (by exact_mod_cast hcast)

private theorem tensorDegreeForget_component_homogeneous (p q n : ℕ) (h : p+q=n)
    (t : degree M p ⊗[ℂ] degree N q) :
    tensorDegreeForget M N n (tensorDegreeComponent M N n
      (tensorDegreeSumEquiv M N (DirectSum.of
        (fun pq : ℕ × ℕ => degree M pq.1 ⊗[ℂ] degree N pq.2) (p,q) t))) =
      tensorDegreeSumEquiv M N (DirectSum.of
        (fun pq : ℕ × ℕ => degree M pq.1 ⊗[ℂ] degree N pq.2) (p,q) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp only [map_add, ht, hu]
  | tmul u v =>
    rw [← DirectSum.lof_eq_of ℂ, tensorDegreeSumEquiv_of_tmul,
      tensorDegreeComponent_subtype_tmul M N p q n h,
      tensorDegreeForget_inclusion, TensorProduct.map_tmul]
    rfl

/-- The actual categorical degree-sum tensor contains every vector of the specified
Euler degree, with the specified finite component map as inverse. -/
theorem tensorDegreeForget_component_of_eigen {n : ℕ}
    {z : RelativeChains M ⊗[ℂ] RelativeChains N}
    (hz : relativeTensorEuler (M := M) (N := N) z = (n : ℂ) • z) :
    tensorDegreeForget M N n (tensorDegreeComponent M N n z) = z := by
  classical
  let w := (tensorDegreeSumEquiv M N).symm z
  have he : z = ∑ pq ∈ w.support, tensorDegreeSumEquiv M N
      (DirectSum.of (fun pq : ℕ × ℕ => degree M pq.1 ⊗[ℂ] degree N pq.2) pq (w pq)) := by
    rw [← map_sum, DirectSum.sum_support_of, LinearEquiv.apply_symm_apply]
  rw [he, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro pq hpq
  have hdeg : pq.1 + pq.2 = n := by
    by_contra hneq
    have hw : w pq = 0 := by
      change (tensorDegreeSumEquiv M N).symm z (pq.1,pq.2) = 0
      rw [tensorDegreeSumEquiv_symm_apply,
        tensorBidegreeComponent_eq_zero_of_eigen M N hneq hz]
    exact (DFinsupp.mem_support_iff.mp hpq) hw
  exact tensorDegreeForget_component_homogeneous M N pq.1 pq.2 n hdeg (w pq)

end KhanSL2.Factorization
