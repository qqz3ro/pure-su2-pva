module

public import KhanSL2.Macdonald.ActualHomologyRootChart

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

/-- The original symmetric coproduct of a represented cycle. -/
def symmetricCoproductCycle (r s : ℕ)
    (z : LinearMap.ker (differential (symmetricPower (r+s)))) :
    LinearMap.ker (relativeTensorDifferential (symmetricPower r) (symmetricPower s)) :=
  ⟨symmetricPowerChainCoproduct r s z.val,by
    change relativeTensorDifferential (symmetricPower r) (symmetricPower s)
      (symmetricPowerChainCoproduct r s z.val) = 0
    rw [← symmetricPowerChainCoproduct_differential,z.property,map_zero]⟩

theorem symmetricPowerCoproductTotalHomology_mk (r s : ℕ)
    (z : LinearMap.ker (differential (symmetricPower (r+s)))) :
    symmetricPowerCoproductTotalHomology r s (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (symmetricCoproductCycle r s z) := rfl

/-- Normalize that same cycle by the coefficient binomial factor. -/
def normalizedSymmetricCoproductCycle (r s : ℕ)
    (z : LinearMap.ker (differential (symmetricPower (r+s)))) :
    LinearMap.ker (relativeTensorDifferential (symmetricPower r) (symmetricPower s)) :=
  (Nat.choose (r+s) r : ℂ)⁻¹ • symmetricCoproductCycle r s z

theorem totalKunnethInverse_apply_symmetric (r s : ℕ)
    (z : TensorTotalHomology (symmetricPower r) (symmetricPower s)) :
    totalKunnethInverse (symmetricPower r) (symmetricPower s) z =
      (totalKunnethEquiv (symmetricPower r) (symmetricPower s)).symm z := rfl

set_option backward.isDefEq.respectTransparency true in
theorem normalizedSymmetricPowerHomologyCoproduct_mk (r s : ℕ)
    (z : LinearMap.ker (differential (symmetricPower (r+s)))) :
    normalizedSymmetricPowerHomologyCoproduct r s (Submodule.Quotient.mk z) =
      (totalKunnethEquiv (symmetricPower r) (symmetricPower s)).symm
        (Submodule.Quotient.mk (normalizedSymmetricCoproductCycle r s z)) := by
  let X := TensorTotalHomology (symmetricPower r) (symmetricPower s)
  let Y := TotalHomology (symmetricPower r) ⊗[ℂ] TotalHomology (symmetricPower s)
  let f : X →ₗ[ℂ] Y := totalKunnethInverse (symmetricPower r) (symmetricPower s)
  let a : ℂ := (Nat.choose (r+s) r : ℂ)⁻¹
  let q : X := Submodule.Quotient.mk (symmetricCoproductCycle r s z)
  have hf : f (a • q) = a • f q := f.map_smul a q
  calc
    normalizedSymmetricPowerHomologyCoproduct r s (Submodule.Quotient.mk z) = a • f q := by
      simp only [normalizedSymmetricPowerHomologyCoproduct, LinearMap.smul_apply,
        symmetricPowerHomologyCoproduct, LinearMap.comp_apply,
        symmetricPowerCoproductTotalHomology_mk, a, f, q]
    _ = f (a • q) := hf.symm
    _ = f (Submodule.Quotient.mk (normalizedSymmetricCoproductCycle r s z)) := rfl
    _ = (totalKunnethEquiv (symmetricPower r) (symmetricPower s)).symm
        (Submodule.Quotient.mk (normalizedSymmetricCoproductCycle r s z)) :=
      totalKunnethInverse_apply_symmetric r s _
end KhanSL2.SymmetricFamily
