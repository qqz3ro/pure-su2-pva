module

public import KhanSL2.Conditional.BGGComplex

@[expose] public section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-! # Canonical homology comparison for the assembled BGG complex -/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Conditional.BGGComplex

open BGGBridge

local instance termAddCommGroup (B p : ℕ) : AddCommGroup (Term B p) := inferInstance
local instance termModule (B p : ℕ) : Module ℂ (Term B p) := inferInstance

abbrev Cycles (B p : ℕ) := Depth.cycles (Term B) (differential B) p
local instance cyclesAddCommGroup (B p : ℕ) : AddCommGroup (Cycles B p) := inferInstance
local instance cyclesModule (B p : ℕ) : Module ℂ (Cycles B p) := inferInstance

abbrev ComponentCycles (B p : ℕ) (S : ℤ) := (bggWindow p B S).cycles
abbrev CycleSum (B p : ℕ) := ⨁ S : ℤ, ↥(ComponentCycles B p S)

/-- The assembled cycle condition is exactly the cycle condition in every spin. -/
theorem mem_cycles_iff (B p : ℕ) (x : Term B p) :
    x ∈ Cycles B p ↔ ∀ S : ℤ, dHq Current.NB (x S) = 0 := by
  cases p with
  | zero =>
    constructor
    · intro _ S
      exact dHq_zero_on_degree_zero B S (x S)
    · intro _
      exact Submodule.mem_top
  | succ p =>
    change differential B p x = 0 ↔ _
    constructor
    · intro hx S
      exact congrArg (fun y : Term B p => ((y S : bggTerm p B S) :
        HarmN Current.NB ⧸ relH Current.NB)) hx
    · intro hx
      apply DFinsupp.ext
      intro S
      exact Subtype.ext (hx S)

/-- Inclusion of the actual cycles of one spin into its chain term. -/
def componentCyclesToTerm (B p : ℕ) (S : ℤ) :
    ComponentCycles B p S →ₗ[ℂ] bggTerm p B S where
  toFun z := ⟨z.val, z.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The sum of homogeneous cycles is an assembled cycle. -/
def sumCyclesToCycles (B p : ℕ) : CycleSum B p →ₗ[ℂ] Cycles B p :=
  (DirectSum.lmap (componentCyclesToTerm B p)).codRestrict (Cycles B p) (by
    intro z
    apply (mem_cycles_iff B p _).mpr
    intro S
    exact (z S).property.2)

@[simp] theorem sumCyclesToCycles_apply (B p : ℕ) (z : CycleSum B p) (S : ℤ) :
    ((sumCyclesToCycles B p z).val S : HarmN Current.NB ⧸ relH Current.NB) =
      (z S).val := rfl

theorem sumCyclesToCycles_bijective (B p : ℕ) : Function.Bijective (sumCyclesToCycles B p) := by
  constructor
  · intro z w h
    have h' := congrArg Subtype.val h
    exact (DirectSum.lmap_injective (componentCyclesToTerm B p)).mpr
      (fun S x y hxy => Subtype.ext (congrArg (fun t : bggTerm p B S => t.val) hxy)) h'
  · intro x
    have hx : x.val ∈ LinearMap.range (DirectSum.lmap (componentCyclesToTerm B p)) := by
      rw [DirectSum.range_lmap, Submodule.mem_comap, Submodule.mem_pi]
      intro S _
      exact ⟨⟨(x.val S).val, (x.val S).property,
        (mem_cycles_iff B p x.val).mp x.property S⟩, rfl⟩
    obtain ⟨z, hz⟩ := hx
    exact ⟨z, Subtype.ext hz⟩

/-- Cycles commute with the algebraic sum over spin. -/
def cyclesEquivSum (B p : ℕ) : Cycles B p ≃ₗ[ℂ] CycleSum B p :=
  (LinearEquiv.ofBijective (sumCyclesToCycles B p) (sumCyclesToCycles_bijective B p)).symm

@[simp] theorem cyclesEquivSum_apply (B p : ℕ) (x : Cycles B p) (S : ℤ) :
    (cyclesEquivSum B p x S).val = (x.val S).val := by
  have h := (cyclesEquivSum B p).symm_apply_apply x
  exact congrArg (fun y : Cycles B p => (y.val S).val) h

/-- Take the actual quotient class in every spin. -/
def cyclesToBGGTotal (B p : ℕ) : Cycles B p →ₗ[ℂ] Modules.BGGHomologyTotal B p :=
  (DirectSum.lmap (fun S : ℤ => (bggWindow p B S).boundaries.mkQ)).comp
    (cyclesEquivSum B p).toLinearMap

theorem cyclesToBGGTotal_surjective (B p : ℕ) : Function.Surjective (cyclesToBGGTotal B p) :=
  ((DirectSum.lmap_surjective (fun S : ℤ => (bggWindow p B S).boundaries.mkQ)).mpr
    (fun S => Submodule.mkQ_surjective (bggWindow p B S).boundaries)).comp (cyclesEquivSum B p).surjective

/-- A component class is zero exactly when its actual cycle is a boundary. -/
theorem component_class_eq_zero_iff (B p : ℕ) (S : ℤ) (z : ComponentCycles B p S) :
    (Submodule.Quotient.mk z : BGGHomology p B S) = 0 ↔
      ∃ w ∈ bggTerm (p + 1) B S, dHq Current.NB w = z.val :=
  Submodule.Quotient.mk_eq_zero (bggWindow p B S).boundaries

/-- Vanishing is checked in each spin without enlarging finite support. -/
theorem cyclesToBGGTotal_eq_zero_iff (B p : ℕ) (x : Cycles B p) :
    cyclesToBGGTotal B p x = 0 ↔
      ∀ S : ℤ, ∃ w ∈ bggTerm (p + 1) B S, dHq Current.NB w = (x.val S).val := by
  constructor
  · intro hx S
    have hs := congrArg (fun z : Modules.BGGHomologyTotal B p => z S) hx
    obtain ⟨w, hw, hwe⟩ := (component_class_eq_zero_iff B p S (cyclesEquivSum B p x S)).mp hs
    exact ⟨w, hw, hwe.trans (cyclesEquivSum_apply B p x S)⟩
  · intro hx
    apply DFinsupp.ext
    intro S
    obtain ⟨w, hw, hwe⟩ := hx S
    exact (component_class_eq_zero_iff B p S (cyclesEquivSum B p x S)).mpr
      ⟨w, hw, hwe.trans (cyclesEquivSum_apply B p x S).symm⟩

/-- Restricting a map does not change the meaning of a preimage in its source submodule. -/
theorem mem_restrict_range_iff {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N) (P : Submodule ℂ M)
    (Q : Submodule ℂ N) (hf : ∀ x ∈ P, f x ∈ Q) (x : Q) :
    x ∈ LinearMap.range (f.restrict hf) ↔ ∃ y ∈ P, f y = x.val := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, y.property, congrArg (fun z : Q => z.val) hy⟩
  · rintro ⟨y, hy, hye⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hye⟩

/-- Membership in the range is checked in each spin. -/
theorem mem_differential_range_iff (B p : ℕ) (x : Term B p) :
    x ∈ LinearMap.range (differential B p) ↔
      ∀ S : ℤ, ∃ w ∈ bggTerm (p + 1) B S, dHq Current.NB w = (x S).val := by
  rw [differential, DirectSum.range_lmap, Submodule.mem_comap, Submodule.mem_pi]
  simp only [Set.mem_univ, forall_const]
  exact forall_congr' (fun S => mem_restrict_range_iff (dHq Current.NB)
    (bggTerm (p + 1) B S) (bggTerm p B S)
    (fun z hz => (bggWindow p B S).differential_mem z hz) (x S))
/-- The kernel consists precisely of actual assembled boundaries. -/
theorem cyclesToBGGTotal_ker (B p : ℕ) :
    LinearMap.ker (cyclesToBGGTotal B p) =
      (LinearMap.range (differential B p)).comap (Cycles B p).subtype := by
  apply Submodule.ext
  intro x
  change cyclesToBGGTotal B p x = 0 ↔ x.val ∈ LinearMap.range (differential B p)
  exact (cyclesToBGGTotal_eq_zero_iff B p x).trans (mem_differential_range_iff B p x.val).symm

/-- The first isomorphism theorem with the prescribed kernel displayed explicitly. -/
def quotientEquivOfKernel {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (P : Submodule ℂ M) (f : M →ₗ[ℂ] N)
    (hf : Function.Surjective f) (hker : LinearMap.ker f = P) : (M ⧸ P) ≃ₗ[ℂ] N :=
  (Submodule.quotEquivOfEq P (LinearMap.ker f) hker.symm).trans
    (f.quotKerEquivOfSurjective hf)

@[simp] theorem quotientEquivOfKernel_mk {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (P : Submodule ℂ M) (f : M →ₗ[ℂ] N)
    (hf : Function.Surjective f) (hker : LinearMap.ker f = P) (x : M) :
    quotientEquivOfKernel P f hf hker (Submodule.Quotient.mk x) = f x := rfl

/-- Homology commutes with the algebraic direct sum, for the specified BGG complex. -/
def homologyEquivBGGTotal (B p : ℕ) : Homology B p ≃ₗ[ℂ] Modules.BGGHomologyTotal B p :=
  quotientEquivOfKernel (M := Cycles B p) (N := Modules.BGGHomologyTotal B p) ((LinearMap.range (differential B p)).comap (Cycles B p).subtype)
    (cyclesToBGGTotal B p) (cyclesToBGGTotal_surjective B p) (cyclesToBGGTotal_ker B p)
/-- The canonical comparison with the actual relative CE coefficient homology. -/
def homologyEquivK (B p : ℕ) : Homology B p ≃ₗ[ℂ] Modules.KTotal B p :=
  (homologyEquivBGGTotal B p).trans (Modules.kTotalEquivBGG B p).symm

/-- On a cycle, the comparison uses the specified BGG bridge separately in every spin. -/
theorem homologyEquivK_mk_component (B p : ℕ) (x : Cycles B p) (S : ℤ) :
    homologyEquivK B p (Submodule.Quotient.mk x) S =
      (Current.kEquivBGGHomology p B S).symm
        (Submodule.Quotient.mk (cyclesEquivSum B p x S)) := rfl

end KhanSL2.Conditional.BGGComplex
