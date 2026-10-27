module

public import KhanSL2.Factorization.KunnethTotalProjection
public import KhanSL2.Factorization.BalancedTensorDifferential

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

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [SymmetricFamily.CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [SymmetricFamily.CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

theorem balancedTensorDegreeComponent_subtype_tmul_ne (p q n : ℕ) (h : p+q ≠ n)
    (u : degree M p) (v : degree N q) :
    balancedTensorDegreeComponent A M N n (u.val ⊗ₜ[A] v.val) = 0 := by
  rw [balancedTensorDegreeComponent_tmul]
  apply Finset.sum_eq_zero
  intro r hr
  have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  rw [dif_pos hrn]
  by_cases hp : r = p
  · subst r
    have hq : n-p ≠ q := by omega
    have hv : coefficientDegreeComponentLinear A N (n-p) v.val = 0 :=
      degreeComponent_subtype_ne N hq v
    rw [hv, TensorProduct.tmul_zero, map_zero]
  · have hu : coefficientDegreeComponentLinear A M r u.val = 0 :=
      degreeComponent_subtype_ne M hp u
    rw [hu, TensorProduct.zero_tmul, map_zero]

/-- The categorical tensor degree and its canonical retraction define the projection. -/
def balancedTensorDegreeProjection (n : ℕ) :
    Module.End A (RelativeChains M ⊗[A] RelativeChains N) :=
  (balancedTensorDegreeForget A M N n).comp (balancedTensorDegreeComponent A M N n)

theorem balancedTensorDegreeProjection_tmul_of_mem {p q : ℕ} {u : RelativeChains M}
    {v : RelativeChains N} (hu : u ∈ degree M p) (hv : v ∈ degree N q) (n : ℕ) :
    balancedTensorDegreeProjection A M N n (u ⊗ₜ[A] v) =
      if p+q=n then u ⊗ₜ[A] v else 0 := by
  change balancedTensorDegreeForget A M N n (balancedTensorDegreeComponent A M N n
    ((⟨u,hu⟩ : degree M p).val ⊗ₜ[A] (⟨v,hv⟩ : degree N q).val)) = _
  by_cases h : p+q=n
  · rw [if_pos h,balancedTensorDegreeComponent_subtype_tmul A M N p q n h,
      balancedTensorDegreeForget_inclusion,TensorProduct.map_tmul]
    rfl
  · rw [if_neg h,balancedTensorDegreeComponent_subtype_tmul_ne A M N p q n h,map_zero]

@[simp] theorem balancedTensorDegreeProjection_forget (n : ℕ) (z : (balancedTensorComplex A M N).X n) :
    balancedTensorDegreeProjection A M N n (balancedTensorDegreeForget A M N n z) =
      balancedTensorDegreeForget A M N n z := by
  rw [balancedTensorDegreeProjection,LinearMap.comp_apply,balancedTensorDegreeComponent_forget]

theorem balancedTensorDegreeComponent_forget_ne {n k : ℕ} (hne : n ≠ k)
    (z : (balancedTensorComplex A M N).X k) :
    balancedTensorDegreeComponent A M N n (balancedTensorDegreeForget A M N k z) = 0 := by
  have h : ModuleCat.ofHom ((balancedTensorDegreeComponent A M N n).comp
      (balancedTensorDegreeForget A M N k)) = 0 := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p+q=k at hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change balancedTensorDegreeComponent A M N n (balancedTensorDegreeForget A M N k
      (balancedTensorDegreeInclusion A M N p q k hpq (u ⊗ₜ[A] v))) = 0
    rw [balancedTensorDegreeForget_inclusion,TensorProduct.map_tmul]
    exact balancedTensorDegreeComponent_subtype_tmul_ne A M N p q n (by omega) u v
  exact congrArg (fun f => f.hom z) h

theorem balancedTensorDegreeProjection_forget_ne {n k : ℕ} (hne : n ≠ k)
    (z : (balancedTensorComplex A M N).X k) :
    balancedTensorDegreeProjection A M N n (balancedTensorDegreeForget A M N k z) = 0 := by
  rw [balancedTensorDegreeProjection,LinearMap.comp_apply,balancedTensorDegreeComponent_forget_ne A M N hne,map_zero]

/-- On each homogeneous tensor the signed boundary has precisely total degree one less. -/
theorem balancedTensorDegreeProjection_boundary_tmul {p q : ℕ} {u : RelativeChains M}
    {v : RelativeChains N} (hu : u ∈ degree M p) (hv : v ∈ degree N q) (n : ℕ) :
    balancedTensorDegreeProjection A M N n (balancedTensorDifferential A M N (u ⊗ₜ[A] v)) =
      if p+q=n+1 then balancedTensorDifferential A M N (u ⊗ₜ[A] v) else 0 := by
  rw [balancedTensorDifferential_tmul,relativeParity_of_mem_degree M hu]
  cases p with
  | zero =>
    rw [differential_eq_zero_of_degree_zero M hu]
    simp only [TensorProduct.zero_tmul,zero_add,pow_zero,one_smul]
    cases q with
    | zero => simp [differential_eq_zero_of_degree_zero N hv]
    | succ q =>
      rw [balancedTensorDegreeProjection_tmul_of_mem A M N hu (differential_mem_degree N hv)]
      simp only [Nat.zero_add,Nat.succ_eq_add_one,Nat.add_right_cancel_iff]
  | succ p =>
    have hd := differential_mem_degree M hu
    cases q with
    | zero =>
      rw [differential_eq_zero_of_degree_zero N hv]
      simp only [TensorProduct.tmul_zero,add_zero]
      rw [balancedTensorDegreeProjection_tmul_of_mem A M N hd hv]
      simp only [Nat.add_zero,Nat.succ_eq_add_one,Nat.add_right_cancel_iff]
    | succ q =>
      have hdv := differential_mem_degree N hv
      rw [← TensorProduct.smul_tmul',map_add,LinearMap.map_smul_of_tower,
        balancedTensorDegreeProjection_tmul_of_mem A M N hd hv,
        balancedTensorDegreeProjection_tmul_of_mem A M N hu hdv]
      by_cases h : (p+1)+(q+1)=n+1
      · rw [if_pos h,if_pos (show p+(q+1)=n by omega),if_pos (show (p+1)+q=n by omega)]
      · rw [if_neg h,if_neg (show p+(q+1)≠n by omega),if_neg (show (p+1)+q≠n by omega),
          smul_zero,zero_add]

/-- The total projection intertwines the actual boundary with the next projection. -/
theorem balancedTensorDegreeProjection_differential (n : ℕ)
    (z : RelativeChains M ⊗[A] RelativeChains N) :
    balancedTensorDegreeProjection A M N n (balancedTensorDifferential A M N z) =
      balancedTensorDifferential A M N (balancedTensorDegreeProjection A M N (n+1) z) := by
  obtain ⟨t,rfl⟩ := (balancedCoefficientMap_surjective A (RelativeChains M) (RelativeChains N)) z
  obtain ⟨w,rfl⟩ := (tensorDegreeSumEquiv M N).surjective t
  induction w using DirectSum.induction_on with
  | zero =>
    rw [(tensorDegreeSumEquiv M N).map_zero]
    simp only [map_zero]
  | add u v hu hv => simp only [map_add,hu,hv]
  | of pq t =>
    rcases pq with ⟨p,q⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add,hu,hv]
    | tmul u v =>
      rw [← DirectSum.lof_eq_of ℂ,tensorDegreeSumEquiv_of_tmul,
        balancedCoefficientMap_tmul,
        balancedTensorDegreeProjection_boundary_tmul A M N u.property v.property,
        balancedTensorDegreeProjection_tmul_of_mem A M N u.property v.property]
      split <;> simp

end KhanSL2.Factorization



