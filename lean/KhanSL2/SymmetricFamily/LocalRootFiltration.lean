module

public import KhanSL2.SymmetricFamily.LocalRootResidue
public import KhanSL2.SymmetricFamily.IdealTensorFiltration
public import KhanSL2.SymmetricFamily.CurrentSlots

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The finite displacement filtration of the actual one-point root/color
family. The literal labelled current modes preserve it, and their difference
from point evaluation raises the filtration. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

abbrev LocalRootColors (k : ℕ) (a : ℂ) := LocalRootAlgebra k a ⊗[ℂ] Color k

/-- The actual finite displacement filtration, before passing to slot invariants. -/
def localRootColorFiltration (k : ℕ) (a : ℂ) (d : ℕ) : Submodule ℂ (LocalRootColors k a) :=
  idealTensorSubmodule (Color k) (localRootIdeal k a ^ d)

@[simp] theorem localRootColorFiltration_zero (k : ℕ) (a : ℂ) :
    localRootColorFiltration k a 0 = ⊤ := by
  simp only [localRootColorFiltration, pow_zero, Ideal.one_eq_top, idealTensorSubmodule_top]

theorem localRootColorFiltration_terminates (k : ℕ) (a : ℂ) :
    ∃ d, localRootColorFiltration k a d = ⊥ :=
  idealTensorSubmodule_terminates (Color k) (localRootIdeal_nilpotent k a)

/-- The specified mode-z^n operator, evaluated in the actual one-point root algebra. -/
def localRootColorMode (k : ℕ) (a : ℂ) (n : ℕ) (D : Module.End ℂ BGG.G) :
    Module.End ℂ (LocalRootColors k a) :=
  ∑ i : Fin k, TensorProduct.map
    (LinearMap.mulLeft ℂ (localRoot k a i ^ n)) (colorSlot k i D)

/-- Its exact deviation from evaluating each root at the support point. -/
def localRootColorDeviation (k : ℕ) (a : ℂ) (n : ℕ) (D : Module.End ℂ BGG.G) :
    Module.End ℂ (LocalRootColors k a) :=
  ∑ i : Fin k, TensorProduct.map
    (LinearMap.mulLeft ℂ (localRoot k a i ^ n -
      algebraMap ℂ (LocalRootAlgebra k a) (a^n))) (colorSlot k i D)

/-- Every literal current-mode slot operator preserves the displacement filtration. -/
theorem localRootColorMode_preserves (k : ℕ) (a : ℂ) (n d : ℕ)
    (D : Module.End ℂ BGG.G) {v : LocalRootColors k a}
    (hv : v ∈ localRootColorFiltration k a d) :
    localRootColorMode k a n D v ∈ localRootColorFiltration k a d := by
  simp only [localRootColorMode, LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro i _
  exact idealTensorSubmodule_map_mul (Color k) _ _ hv

/-- Deviations from evaluation strictly raise the actual finite filtration. -/
theorem localRootColorDeviation_raises (k : ℕ) (a : ℂ) (n d : ℕ)
    (D : Module.End ℂ BGG.G) {v : LocalRootColors k a}
    (hv : v ∈ localRootColorFiltration k a d) :
    localRootColorDeviation k a n D v ∈ localRootColorFiltration k a (d+1) := by
  simp only [localRootColorDeviation, LinearMap.sum_apply, localRootColorFiltration, pow_succ']
  apply Submodule.sum_mem
  intro i _
  exact idealTensorSubmodule_map_mul_mem (Color k) (localRoot_power_sub_mem k n a i) _ hv

/-- The deviation operator is the literal mode minus its support-point evaluation. -/
theorem localRootColorDeviation_eq (k : ℕ) (a : ℂ) (n : ℕ) (D : Module.End ℂ BGG.G) :
    localRootColorDeviation k a n D =
      localRootColorMode k a n D - (a^n) • localRootColorMode k a 0 D := by
  apply TensorProduct.ext'
  intro q v
  change localRootColorDeviation k a n D (q ⊗ₜ[ℂ] v) =
    localRootColorMode k a n D (q ⊗ₜ[ℂ] v) -
      (a^n) • localRootColorMode k a 0 D (q ⊗ₜ[ℂ] v)
  simp only [localRootColorDeviation, localRootColorMode, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, TensorProduct.map_tmul,
    LinearMap.mulLeft_apply, pow_zero, one_mul, sub_mul,
    TensorProduct.sub_tmul, Finset.sum_sub_distrib, Finset.smul_sum,
    TensorProduct.smul_tmul', Algebra.smul_def]

/-- Summing the literal color slots is the original diagonal color action. -/
theorem colorSlot_sum (k : ℕ) (D : Module.End ℂ BGG.G) :
    (∑ i : Fin k, colorSlot k i D) = colorDeriv k D := by
  apply (Pi.basisFun ℂ (Fin k → Fin 3)).ext
  intro c
  simp only [LinearMap.sum_apply, colorSlot_basis, colorDeriv_basis]

/-- The constant-current operator is exactly the finite color action. -/
theorem localRootColorMode_zero (k : ℕ) (a : ℂ) (D : Module.End ℂ BGG.G) :
    localRootColorMode k a 0 D = LinearMap.lTensor (LocalRootAlgebra k a) (colorDeriv k D) := by
  apply TensorProduct.ext'
  intro q v
  simp only [localRootColorMode, LinearMap.sum_apply, TensorProduct.map_tmul,
    LinearMap.mulLeft_apply, pow_zero, one_mul, LinearMap.lTensor_tmul]
  rw [← TensorProduct.tmul_sum]
  have h := LinearMap.congr_fun (colorSlot_sum k D) v
  simp only [LinearMap.sum_apply] at h
  exact congrArg (fun c => q ⊗ₜ[ℂ] c) h

end KhanSL2.SymmetricFamily
