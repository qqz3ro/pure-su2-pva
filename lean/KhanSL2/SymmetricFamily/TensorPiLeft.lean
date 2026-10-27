module

public import Mathlib.LinearAlgebra.TensorProduct.Pi

@[expose] public section

/-! Finite product distribution over the smaller ground field, retaining the
larger coefficient ring's linear structure. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily

variable (K : Type*) [CommRing K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module K (M i)]
variable (W : Type*) [AddCommGroup W] [Module K W]

/-- The underlying finite-product equivalence, written on every pure tensor. -/
theorem tensorPiLeft_tmul (m : ∀ i, M i) (w : W) :
    TensorProduct.piLeft K W M (m ⊗ₜ[K] w) = fun i => m i ⊗ₜ[K] w := by
  funext i
  simp

variable (A : Type*) [CommRing A] [Algebra K A]
  [∀ i, Module A (M i)] [∀ i, IsScalarTower K A (M i)]

/-- Finite tensor/product distribution is linear over the original coefficient ring. -/
def tensorPiLeftEquiv : (∀ i, M i) ⊗[K] W ≃ₗ[A] ∀ i, M i ⊗[K] W where
  __ := (TensorProduct.piLeft K W M).toAddEquiv
  map_smul' a x := by
    change TensorProduct.piLeft K W M (a • x) = a • TensorProduct.piLeft K W M x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m w =>
      rw [TensorProduct.smul_tmul', tensorPiLeft_tmul, tensorPiLeft_tmul]
      rfl

@[simp] theorem tensorPiLeftEquiv_tmul (m : ∀ i, M i) (w : W) :
    tensorPiLeftEquiv K M W A (m ⊗ₜ[K] w) = fun i => m i ⊗ₜ[K] w :=
  tensorPiLeft_tmul K M W m w

end KhanSL2.SymmetricFamily
