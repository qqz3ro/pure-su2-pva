module

public import KhanSL2.Injectivity.ExteriorSubstitution
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

@[expose] public section

/-! The concrete ordered-monomial exterior algebra is the usual exterior
algebra on the free vector space of generators. This comparison allows
library constructions on exterior powers to be transported to concrete CE
coordinates without postulating their universal property. -/

noncomputable section
namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

/-- Insert a finitely supported vector as an exterior element of degree one. -/
def generatorLinear : (α →₀ ℂ) →ₗ[ℂ] Exterior α :=
  Finsupp.linearCombination ℂ generator

@[simp] theorem generatorLinear_single (a : α) (r : ℂ) :
    generatorLinear (Finsupp.single a r) = r • generator a := by
  simp [generatorLinear]

theorem parity_generatorLinear (v : α →₀ ℂ) :
    parityLinear (generatorLinear v) = -generatorLinear v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, add_comm]
  | single a r => simp

/-- Algebra maps out of the concrete model are determined by its generators. -/
theorem algHom_ext {A : Type*} [Ring A] [Algebra ℂ A]
    (f g : Exterior α →ₐ[ℂ] A)
    (h : ∀ a, f (generator a) = g (generator a)) : f = g := by
  apply AlgHom.ext
  intro v
  refine induction_on (GeneratorOrder.code (α := α))
    (P := fun w : Exterior α => f w = g w) ?_ ?_ ?_ ?_ ?_ v
  · simp
  · change f 1 = g 1
    simp
  · intro u v hu hv
    simp only [map_add, hu, hv]
  · intro r u hu
    simp only [map_smul, hu]
  · intro a u hu
    change f (generator a * u) = g (generator a * u)
    simp only [map_mul, h, hu]
/-- The usual exterior algebra maps to the concrete ordered-monomial model. -/
def fromMathlibExterior : ExteriorAlgebra ℂ (α →₀ ℂ) →ₐ[ℂ] Exterior α :=
  ExteriorAlgebra.lift ℂ ⟨generatorLinear,
    fun v => odd_sq_zero (generatorLinear v) (parity_generatorLinear v)⟩

@[simp] theorem fromMathlibExterior_ι (v : α →₀ ℂ) :
    fromMathlibExterior (ExteriorAlgebra.ι ℂ v) = generatorLinear v :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

/-- Substitute the universal generators into the concrete model. -/
def toMathlibExterior : Exterior α →ₐ[ℂ] ExteriorAlgebra ℂ (α →₀ ℂ) :=
  substitute (fun a => ExteriorAlgebra.ι ℂ (Finsupp.single a 1))
    (fun a => ExteriorAlgebra.ι_sq_zero (Finsupp.single a 1))
    (fun a b => eq_neg_of_add_eq_zero_left
      (ExteriorAlgebra.ι_add_mul_swap (Finsupp.single a 1) (Finsupp.single b 1)))

@[simp] theorem toMathlibExterior_generator (a : α) :
    toMathlibExterior (generator a) = ExteriorAlgebra.ι ℂ (Finsupp.single a 1) :=
  substitute_generator _ _ _ a

theorem fromMathlibExterior_comp_toMathlibExterior :
    (fromMathlibExterior (α := α)).comp toMathlibExterior = AlgHom.id ℂ (Exterior α) := by
  apply algHom_ext
  intro a
  simp

theorem toMathlibExterior_generatorLinear (v : α →₀ ℂ) :
    toMathlibExterior (generatorLinear v) = ExteriorAlgebra.ι ℂ v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw, add_comm]
  | single a r =>
    rw [generatorLinear_single, map_smul, toMathlibExterior_generator]
    rw [← map_smul]
    congr 1
    simp

theorem toMathlibExterior_comp_fromMathlibExterior :
    (toMathlibExterior (α := α)).comp fromMathlibExterior =
      AlgHom.id ℂ (ExteriorAlgebra ℂ (α →₀ ℂ)) := by
  apply ExteriorAlgebra.hom_ext
  apply LinearMap.ext
  intro v
  change toMathlibExterior (fromMathlibExterior (ExteriorAlgebra.ι ℂ v)) = _
  rw [fromMathlibExterior_ι, toMathlibExterior_generatorLinear]
  rfl

/-- A proved algebra equivalence with mathlib's universal exterior algebra. -/
def exteriorAlgebraEquiv : Exterior α ≃ₐ[ℂ] ExteriorAlgebra ℂ (α →₀ ℂ) :=
  AlgEquiv.ofAlgHom toMathlibExterior fromMathlibExterior
    toMathlibExterior_comp_fromMathlibExterior fromMathlibExterior_comp_toMathlibExterior

@[simp] theorem exteriorAlgebraEquiv_generator (a : α) :
    exteriorAlgebraEquiv (generator a) = ExteriorAlgebra.ι ℂ (Finsupp.single a 1) :=
  toMathlibExterior_generator a

end KhanSL2.FiniteExterior