module

public import KhanSL2.Factorization.KunnethTensorBigrading
public import KhanSL2.Factorization.KunnethTensorDifferential

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual total-degree projections on the signed tensor of relative CE chains,
including the exact shifted boundary identity. -/

noncomputable section
open scoped TensorProduct DirectSum BigOperators
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

theorem tensorDegreeComponent_subtype_tmul_ne (p q n : ℕ) (h : p+q ≠ n)
    (u : degree M p) (v : degree N q) :
    tensorDegreeComponent M N n (u.val ⊗ₜ[ℂ] v.val) = 0 := by
  rw [tensorDegreeComponent_tmul]
  apply Finset.sum_eq_zero
  intro r hr
  have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [dif_pos hrn]
  by_cases hp : r = p
  · subst r
    have hq : n-p ≠ q := by omega
    rw [degreeComponent_subtype_ne N hq, TensorProduct.tmul_zero, map_zero]
  · rw [degreeComponent_subtype_ne M hp, TensorProduct.zero_tmul, map_zero]

/-- The categorical tensor degree and its canonical retraction define the projection. -/
def tensorDegreeProjection (n : ℕ) :
    Module.End ℂ (RelativeChains M ⊗[ℂ] RelativeChains N) :=
  (tensorDegreeForget M N n).comp (tensorDegreeComponent M N n)

theorem tensorDegreeProjection_tmul_of_mem {p q : ℕ} {u : RelativeChains M}
    {v : RelativeChains N} (hu : u ∈ degree M p) (hv : v ∈ degree N q) (n : ℕ) :
    tensorDegreeProjection M N n (u ⊗ₜ[ℂ] v) =
      if p+q=n then u ⊗ₜ[ℂ] v else 0 := by
  change tensorDegreeForget M N n (tensorDegreeComponent M N n
    ((⟨u,hu⟩ : degree M p).val ⊗ₜ[ℂ] (⟨v,hv⟩ : degree N q).val)) = _
  by_cases h : p+q=n
  · rw [if_pos h,tensorDegreeComponent_subtype_tmul M N p q n h,
      tensorDegreeForget_inclusion,TensorProduct.map_tmul]
    rfl
  · rw [if_neg h,tensorDegreeComponent_subtype_tmul_ne M N p q n h,map_zero]

@[simp] theorem tensorDegreeProjection_forget (n : ℕ) (z : (tensorComplex M N).X n) :
    tensorDegreeProjection M N n (tensorDegreeForget M N n z) =
      tensorDegreeForget M N n z := by
  rw [tensorDegreeProjection,LinearMap.comp_apply,tensorDegreeComponent_forget]

theorem tensorDegreeComponent_forget_ne {n k : ℕ} (hne : n ≠ k)
    (z : (tensorComplex M N).X k) :
    tensorDegreeComponent M N n (tensorDegreeForget M N k z) = 0 := by
  have h : ModuleCat.ofHom ((tensorDegreeComponent M N n).comp
      (tensorDegreeForget M N k)) = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p+q=k at hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change tensorDegreeComponent M N n (tensorDegreeForget M N k
      (tensorDegreeInclusion M N p q k hpq (u ⊗ₜ[ℂ] v))) = 0
    rw [tensorDegreeForget_inclusion,TensorProduct.map_tmul]
    exact tensorDegreeComponent_subtype_tmul_ne M N p q n (by omega) u v
  exact congrArg (fun f => f.hom z) h

theorem tensorDegreeProjection_forget_ne {n k : ℕ} (hne : n ≠ k)
    (z : (tensorComplex M N).X k) :
    tensorDegreeProjection M N n (tensorDegreeForget M N k z) = 0 := by
  rw [tensorDegreeProjection,LinearMap.comp_apply,tensorDegreeComponent_forget_ne M N hne,map_zero]

/-- On each homogeneous tensor the signed boundary has precisely total degree one less. -/
theorem tensorDegreeProjection_boundary_tmul {p q : ℕ} {u : RelativeChains M}
    {v : RelativeChains N} (hu : u ∈ degree M p) (hv : v ∈ degree N q) (n : ℕ) :
    tensorDegreeProjection M N n (relativeTensorDifferential M N (u ⊗ₜ[ℂ] v)) =
      if p+q=n+1 then relativeTensorDifferential M N (u ⊗ₜ[ℂ] v) else 0 := by
  rw [relativeTensorDifferential_tmul,relativeParity_of_mem_degree M hu]
  cases p with
  | zero =>
    rw [differential_eq_zero_of_degree_zero M hu]
    simp only [TensorProduct.zero_tmul,zero_add,pow_zero,one_smul]
    cases q with
    | zero => simp [differential_eq_zero_of_degree_zero N hv]
    | succ q =>
      rw [tensorDegreeProjection_tmul_of_mem M N hu (differential_mem_degree N hv)]
      simp only [Nat.zero_add,Nat.succ_eq_add_one,Nat.add_right_cancel_iff]
  | succ p =>
    have hd := differential_mem_degree M hu
    cases q with
    | zero =>
      rw [differential_eq_zero_of_degree_zero N hv]
      simp only [TensorProduct.tmul_zero,add_zero]
      rw [tensorDegreeProjection_tmul_of_mem M N hd hv]
      simp only [Nat.add_zero,Nat.succ_eq_add_one,Nat.add_right_cancel_iff]
    | succ q =>
      have hdv := differential_mem_degree N hv
      rw [← TensorProduct.smul_tmul',map_add,map_smul,
        tensorDegreeProjection_tmul_of_mem M N hd hv,
        tensorDegreeProjection_tmul_of_mem M N hu hdv]
      by_cases h : (p+1)+(q+1)=n+1
      · rw [if_pos h,if_pos (show p+(q+1)=n by omega),if_pos (show (p+1)+q=n by omega)]
      · rw [if_neg h,if_neg (show p+(q+1)≠n by omega),if_neg (show (p+1)+q≠n by omega),
          smul_zero,zero_add]

/-- The total projection intertwines the actual boundary with the next projection. -/
theorem tensorDegreeProjection_differential (n : ℕ)
    (z : RelativeChains M ⊗[ℂ] RelativeChains N) :
    tensorDegreeProjection M N n (relativeTensorDifferential M N z) =
      relativeTensorDifferential M N (tensorDegreeProjection M N (n+1) z) := by
  obtain ⟨w,rfl⟩ := (tensorDegreeSumEquiv M N).surjective z
  induction w using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of pq t =>
    rcases pq with ⟨p,q⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add,hu,hv]
    | tmul u v =>
      rw [← DirectSum.lof_eq_of ℂ,tensorDegreeSumEquiv_of_tmul,
        tensorDegreeProjection_boundary_tmul M N u.property v.property,
        tensorDegreeProjection_tmul_of_mem M N u.property v.property]
      split <;> simp

end KhanSL2.Factorization
