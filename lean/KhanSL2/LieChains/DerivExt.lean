module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold

@[expose] public section

/-!
# Derivation extensions to the exterior algebra

Every linear endomorphism `D` of a module `L` extends uniquely to a derivation
`derivExt D` of the exterior algebra `ΛL` with `derivExt D (ι y) = ι (D y)`.
It is defined by `CliffordAlgebra.foldr'` through the recursion
`derivExt D (ι y * x) = ι (D y) * x + ι y * derivExt D x`.
-/

noncomputable section

namespace KhanSL2.LieChains

open ExteriorAlgebra

variable {k L : Type*} [CommRing k] [AddCommGroup L] [Module k L]

/-- One step of the derivation recursion. -/
def derivStep (D : Module.End k L) :
    L →ₗ[k] (ExteriorAlgebra k L × ExteriorAlgebra k L) →ₗ[k] ExteriorAlgebra k L :=
  ((LinearMap.mul k (ExteriorAlgebra k L)) ∘ₗ (ι k) ∘ₗ D).compl₂
      (LinearMap.fst k (ExteriorAlgebra k L) (ExteriorAlgebra k L)) +
    ((LinearMap.mul k (ExteriorAlgebra k L)) ∘ₗ (ι k)).compl₂
      (LinearMap.snd k (ExteriorAlgebra k L) (ExteriorAlgebra k L))

theorem derivStep_apply (D : Module.End k L) (y : L)
    (p : ExteriorAlgebra k L × ExteriorAlgebra k L) :
    derivStep D y p = ι k (D y) * p.1 + ι k y * p.2 := rfl

theorem derivStep_cond (D : Module.End k L) (y : L) (x fx : ExteriorAlgebra k L) :
    derivStep D y (CliffordAlgebra.ι (0 : QuadraticForm k L) y * x, derivStep D y (x, fx)) =
      (0 : QuadraticForm k L) y • fx := by
  change ι k (D y) * (ι k y * x) + ι k y * (ι k (D y) * x + ι k y * fx) = _
  rw [QuadraticMap.zero_apply, zero_smul, mul_add, ← mul_assoc, ← mul_assoc, ← mul_assoc,
    ι_sq_zero, zero_mul, add_zero, ← add_mul, ι_add_mul_swap, zero_mul]

/-- The derivation of `ΛL` extending `D`. -/
def derivExt (D : Module.End k L) : Module.End k (ExteriorAlgebra k L) :=
  CliffordAlgebra.foldr' (0 : QuadraticForm k L) (derivStep D) (derivStep_cond D) 0

@[simp] theorem derivExt_algebraMap (D : Module.End k L) (r : k) :
    derivExt D (algebraMap k (ExteriorAlgebra k L) r) = 0 := by
  rw [derivExt, CliffordAlgebra.foldr'_algebraMap, smul_zero]

@[simp] theorem derivExt_one (D : Module.End k L) : derivExt D 1 = 0 := by
  simpa using derivExt_algebraMap D 1

theorem derivExt_ι_mul (D : Module.End k L) (y : L) (x : ExteriorAlgebra k L) :
    derivExt D (ι k y * x) = ι k (D y) * x + ι k y * derivExt D x := by
  rw [derivExt, CliffordAlgebra.foldr'_ι_mul]
  rfl

@[simp] theorem derivExt_ι (D : Module.End k L) (y : L) :
    derivExt D (ι k y) = ι k (D y) := by
  simpa using derivExt_ι_mul D y 1

theorem derivExt_add (D D' : Module.End k L) (x : ExteriorAlgebra k L) :
    derivExt (D + D') x = derivExt D x + derivExt D' x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | ι_mul x y hx =>
    simp only [derivExt_ι_mul, hx, LinearMap.add_apply, map_add, mul_add, add_mul]
    abel

theorem derivExt_smul (c : k) (D : Module.End k L) (x : ExteriorAlgebra k L) :
    derivExt (c • D) x = c • derivExt D x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  | ι_mul x y hx =>
    simp only [derivExt_ι_mul, hx, LinearMap.smul_apply, map_smul, smul_add,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm]

/-- `derivExt` is linear in the endomorphism. -/
def derivExtₗ : Module.End k L →ₗ[k] Module.End k (ExteriorAlgebra k L) where
  toFun := derivExt
  map_add' D D' := LinearMap.ext (derivExt_add D D')
  map_smul' c D := LinearMap.ext (derivExt_smul c D)

@[simp] theorem derivExtₗ_apply (D : Module.End k L) : derivExtₗ D = derivExt D := rfl

/-- The commutator of two derivation extensions extends the commutator. -/
theorem derivExt_commutator (D D' : Module.End k L) (x : ExteriorAlgebra k L) :
    derivExt D (derivExt D' x) - derivExt D' (derivExt D x) =
      derivExt (D * D' - D' * D) x := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add x y hx hy => simp only [map_add, ← hx, ← hy]; abel
  | ι_mul x y hx =>
    simp only [derivExt_ι_mul, map_add, ← hx, LinearMap.sub_apply, Module.End.mul_apply,
      map_sub, mul_sub, sub_mul]
    abel

/-- `derivExt D` is a derivation. -/
theorem derivExt_mul (D : Module.End k L) (x z : ExteriorAlgebra k L) :
    derivExt D (x * z) = derivExt D x * z + x * derivExt D z := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [derivExt_algebraMap, zero_mul, zero_add, ← Algebra.smul_def, map_smul,
      Algebra.smul_def]
  | add x y hx hy => simp only [add_mul, map_add, hx, hy]; abel
  | ι_mul x y hx =>
    rw [mul_assoc, derivExt_ι_mul, derivExt_ι_mul, hx]
    simp only [mul_add, add_mul, mul_assoc]
    abel

theorem derivExt_mem_exteriorPower (D : Module.End k L) {n : ℕ} {x : ExteriorAlgebra k L}
    (hx : x ∈ ⋀[k]^n L) : derivExt D x ∈ ⋀[k]^n L := by
  induction n generalizing x with
  | zero =>
    rw [exteriorPower, pow_zero, Submodule.mem_one] at hx
    obtain ⟨r, rfl⟩ := hx
    simp only [Algebra.linearMap_apply, derivExt_algebraMap]
    exact Submodule.zero_mem _
  | succ n ih =>
    rw [exteriorPower, pow_succ'] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      obtain ⟨y, rfl⟩ := ha
      rw [derivExt_ι_mul]
      refine Submodule.add_mem _ ?_ ?_
      · rw [exteriorPower, pow_succ']
        exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hb
      · rw [exteriorPower, pow_succ']
        exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (ih hb)
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb

end KhanSL2.LieChains
