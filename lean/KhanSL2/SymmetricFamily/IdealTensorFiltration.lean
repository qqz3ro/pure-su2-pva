module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

/-! Ideal filtrations on an actual root algebra tensored with a color module.
All preservation and filtration-raising statements concern the literal tensor
endomorphisms, so they can be applied to the current-mode formulas. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily

variable {Q : Type*} [CommRing Q] [Algebra ℂ Q]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

/-- The color tensors whose root coefficients belong to the specified ideal. -/
def idealTensorSubmodule (I : Ideal Q) : Submodule ℂ (Q ⊗[ℂ] V) :=
  Submodule.span ℂ {x | ∃ q ∈ I, ∃ v : V, x = q ⊗ₜ[ℂ] v}

theorem idealTensorSubmodule_tmul {I : Ideal Q} {q : Q} (hq : q ∈ I) (v : V) :
    q ⊗ₜ[ℂ] v ∈ idealTensorSubmodule V I :=
  Submodule.subset_span ⟨q,hq,v,rfl⟩

theorem idealTensorSubmodule_mono {I J : Ideal Q} (h : I ≤ J) :
    idealTensorSubmodule V I ≤ idealTensorSubmodule V J := by
  apply Submodule.span_le.mpr
  rintro x ⟨q,hq,v,rfl⟩
  exact idealTensorSubmodule_tmul V (h hq) v

@[simp] theorem idealTensorSubmodule_bot : idealTensorSubmodule V (⊥ : Ideal Q) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨q,hq,v,rfl⟩
  have hq0 : q = 0 := hq
  rw [hq0, TensorProduct.zero_tmul]
  exact (⊥ : Submodule ℂ (Q ⊗[ℂ] V)).zero_mem

@[simp] theorem idealTensorSubmodule_top : idealTensorSubmodule V (⊤ : Ideal Q) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | tmul q v => exact idealTensorSubmodule_tmul V (Submodule.mem_top) v

/-- Root multiplication preserves the actual ideal filtration. -/
theorem idealTensorSubmodule_mul {I : Ideal Q} (b : Q) {x : Q ⊗[ℂ] V}
    (hx : x ∈ idealTensorSubmodule V I) :
    LinearMap.rTensor V (LinearMap.mulLeft ℂ b) x ∈ idealTensorSubmodule V I := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,v,rfl⟩ := hy
    exact idealTensorSubmodule_tmul V (I.mul_mem_left b hq) v
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- Any color operator preserves the actual ideal filtration. -/
theorem idealTensorSubmodule_color {I : Ideal Q} (D : Module.End ℂ V) {x : Q ⊗[ℂ] V}
    (hx : x ∈ idealTensorSubmodule V I) :
    LinearMap.lTensor Q D x ∈ idealTensorSubmodule V I := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,v,rfl⟩ := hy
    exact idealTensorSubmodule_tmul V hq (D v)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- A root multiplier in J raises I into the actual product ideal JI. -/
theorem idealTensorSubmodule_mul_mem {I J : Ideal Q} {b : Q} (hb : b ∈ J)
    {x : Q ⊗[ℂ] V} (hx : x ∈ idealTensorSubmodule V I) :
    LinearMap.rTensor V (LinearMap.mulLeft ℂ b) x ∈ idealTensorSubmodule V (J*I) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,v,rfl⟩ := hy
    exact idealTensorSubmodule_tmul V (Ideal.mul_mem_mul hb hq) v
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- A simultaneous root multiplier and color map preserves the ideal filtration. -/
theorem idealTensorSubmodule_map_mul {I : Ideal Q} (b : Q) (D : Module.End ℂ V)
    {x : Q ⊗[ℂ] V} (hx : x ∈ idealTensorSubmodule V I) :
    TensorProduct.map (LinearMap.mulLeft ℂ b) D x ∈ idealTensorSubmodule V I := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,v,rfl⟩ := hy
    exact idealTensorSubmodule_tmul V (I.mul_mem_left b hq) (D v)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- A simultaneous color map does not affect the ideal raised by a root multiplier. -/
theorem idealTensorSubmodule_map_mul_mem {I J : Ideal Q} {b : Q} (hb : b ∈ J)
    (D : Module.End ℂ V) {x : Q ⊗[ℂ] V} (hx : x ∈ idealTensorSubmodule V I) :
    TensorProduct.map (LinearMap.mulLeft ℂ b) D x ∈ idealTensorSubmodule V (J*I) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨q,hq,v,rfl⟩ := hy
    exact idealTensorSubmodule_tmul V (Ideal.mul_mem_mul hb hq) (D v)
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa only [map_smul] using Submodule.smul_mem _ c hx

/-- A nilpotent root ideal gives a terminating actual tensor filtration. -/
theorem idealTensorSubmodule_terminates {I : Ideal Q} (hI : IsNilpotent I) :
    ∃ n : ℕ, idealTensorSubmodule V (I^n) = ⊥ := by
  obtain ⟨n,hn⟩ := hI
  exact ⟨n, by rw [hn]; exact idealTensorSubmodule_bot V⟩

end KhanSL2.SymmetricFamily
