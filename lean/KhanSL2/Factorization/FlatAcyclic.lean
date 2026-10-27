module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section
noncomputable section
open TensorProduct
namespace KhanSL2.Factorization.FlatAcyclic

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The kernel of a surjection between flat modules is flat. -/
theorem kernel_flat_of_surjective [Module.Flat R M] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Flat R (LinearMap.ker f) := by
  apply Module.Flat.iff_rTensor_preserves_injective_linearMap.mpr
  intro P Q _ _ _ _ u hu
  apply Function.Injective.of_comp (f := (LinearMap.ker f).subtype.lTensor Q)
  have hc : ((LinearMap.ker f).subtype.lTensor Q).comp (u.rTensor (LinearMap.ker f)) =
      (u.rTensor M).comp ((LinearMap.ker f).subtype.lTensor P) := by
    rw [LinearMap.lTensor_comp_rTensor,LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.coe_comp,hc,LinearMap.coe_comp]
  exact (Module.Flat.rTensor_preserves_injective_linearMap u hu).comp
    (LinearMap.lTensor_injective_of_exact_of_flat f hf (LinearMap.ker f).subtype
      Subtype.val_injective (LinearMap.exact_subtype_ker_map f) P)

theorem kernel_flat_of_flat_range [Module.Flat R M]
    (f : M →ₗ[R] N) [Module.Flat R (LinearMap.range f)] :
    Module.Flat R (LinearMap.ker f) := by
  let := kernel_flat_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofEq _ _ f.ker_rangeRestrict).symm

variable {L : Type*} [AddCommGroup L] [Module R L]

/-- Right exactness plus a flat cokernel controls the middle term after
arbitrary tensoring. No flatness of the specializing module is required. -/
theorem lTensor_exact_of_flat_cokernel (f : M →ₗ[R] N) (g : L →ₗ[R] M)
    (h : Function.Exact g f) [Module.Flat R (N ⧸ LinearMap.range f)]
    (S : Type*) [AddCommGroup S] [Module R S] :
    Function.Exact (g.lTensor S) (f.lTensor S) := by
  have hex : Function.Exact g f.rangeRestrict := by
    rw [LinearMap.exact_iff,LinearMap.ker_rangeRestrict]
    exact LinearMap.exact_iff.mp h
  have hinj : Function.Injective ((LinearMap.range f).subtype.lTensor S) :=
    LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) (LinearMap.range f).subtype Subtype.val_injective
      (LinearMap.exact_subtype_mkQ _) S
  have hfactor : (LinearMap.range f).subtype.comp f.rangeRestrict = f := rfl
  intro x
  rw [← hfactor,LinearMap.lTensor_comp,LinearMap.comp_apply]
  rw [← map_zero ((LinearMap.range f).subtype.lTensor S),hinj.eq_iff]
  exact _root_.lTensor_exact S hex f.surjective_rangeRestrict x

section Complex
variable (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
variable [∀ n, Module.Flat R (C n)]
variable (d : ∀ n, C (n+1) →ₗ[R] C n)
variable (h₀ : Function.Surjective (d 0))
variable (h : ∀ n, Function.Exact (d (n+1)) (d n))
include h₀ h

/-- Bottom-up cycle flatness for a nonnegative acyclic flat complex. -/
theorem range_flat (n : ℕ) : Module.Flat R (LinearMap.range (d n)) := by
  induction n with
  | zero =>
    let e : LinearMap.range (d 0) ≃ₗ[R] C 0 :=
      LinearEquiv.ofBijective (LinearMap.range (d 0)).subtype
        ⟨Subtype.val_injective,fun y => ⟨⟨y,h₀ y⟩,rfl⟩⟩
    exact Module.Flat.of_linearEquiv e
  | succ n ih =>
    let := ih
    let := kernel_flat_of_flat_range (d n)
    exact Module.Flat.of_linearEquiv
      (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp (h n))).symm

theorem cokernel_flat (n : ℕ) : Module.Flat R (C n ⧸ LinearMap.range (d n)) := by
  cases n with
  | zero =>
    have hs : Subsingleton (C 0 ⧸ LinearMap.range (d 0)) :=
      Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr h₀)
    let := hs
    infer_instance
  | succ n =>
    let := range_flat C d h₀ h n
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp (h n)).symm).trans
        (d n).quotKerEquivRange)

/-- An acyclic nonnegative termwise-flat complex stays acyclic after arbitrary
base change. This includes nonreduced/thickened residue specializations. -/
theorem lTensor_exact (S : Type*) [AddCommGroup S] [Module R S] :
    Function.Surjective ((d 0).lTensor S) ∧
      ∀ n, Function.Exact ((d (n+1)).lTensor S) ((d n).lTensor S) := by
  refine ⟨(d 0).lTensor_surjective S h₀,fun n => ?_⟩
  let := cokernel_flat C d h₀ h n
  exact lTensor_exact_of_flat_cokernel (d n) (d (n+1)) (h n) S

end Complex
end KhanSL2.Factorization.FlatAcyclic
