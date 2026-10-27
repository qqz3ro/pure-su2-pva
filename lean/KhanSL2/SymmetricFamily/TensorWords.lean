module

public import KhanSL2.SymmetricFamily.PolynomialWords
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Normalized symmetric coefficients as the actual invariant tensors of the
polynomial current Lie algebra. The slot action is PiTensorProduct.reindex. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- The tensor basis induced by the actual mode-color basis of currents. -/
def currentWordBasis (k : ℕ) :
    Module.Basis (Fin k → Macdonald.Mode) ℂ (⨂[ℂ]^k BGG.Current) :=
  Basis.piTensorProduct (fun _ : Fin k => symmetricCurrentBasis)

@[simp] theorem currentWordBasis_apply (k : ℕ) (u : Fin k → Macdonald.Mode) :
    currentWordBasis k u = PiTensorProduct.tprod ℂ (fun i => symmetricCurrentBasis (u i)) :=
  Basis.piTensorProduct_apply _ _

/-- Relabel tensor slots by precomposition, agreeing with the word convention. -/
def tensorPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (⨂[ℂ]^k BGG.Current) ≃ₗ[ℂ] (⨂[ℂ]^k BGG.Current) :=
  PiTensorProduct.reindex ℂ (fun _ : Fin k => BGG.Current) σ.symm

@[simp] theorem tensorPermute_tprod {k : ℕ} (σ : Equiv.Perm (Fin k))
    (v : Fin k → BGG.Current) :
    tensorPermute σ (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (v ∘ σ) := by
  simp [tensorPermute, PiTensorProduct.reindex_tprod, Function.comp_def]

/-- Coordinates intertwine the actual slot permutation and permutation of words. -/
theorem currentWordBasis_repr_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k BGG.Current) :
    (currentWordBasis k).repr (tensorPermute σ x) =
      wordPermute σ ((currentWordBasis k).repr x) := by
  have h : (currentWordBasis k).repr.toLinearMap.comp (tensorPermute σ).toLinearMap =
      (wordPermute σ).comp (currentWordBasis k).repr.toLinearMap := by
    apply (currentWordBasis k).ext
    intro u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      wordPermute_single]
    rw [currentWordBasis_apply, tensorPermute_tprod]
    simpa only [currentWordBasis_apply, Function.comp_def] using
      (Module.Basis.repr_self (currentWordBasis k) (u ∘ σ))
  exact LinearMap.congr_fun h x

/-- Invariant current tensors, represented through their faithful word coordinates. -/
def invariantTensors (k : ℕ) : Submodule ℂ (⨂[ℂ]^k BGG.Current) :=
  (invariantWords (α := Macdonald.Mode) k).comap (currentWordBasis k).repr.toLinearMap

/-- The invariant condition is exactly invariance under the actual tensor slot action. -/
theorem mem_invariantTensors_iff (k : ℕ) (x : ⨂[ℂ]^k BGG.Current) :
    x ∈ invariantTensors k ↔ ∀ σ : Equiv.Perm (Fin k), tensorPermute σ x = x := by
  change (∀ σ, wordPermute σ ((currentWordBasis k).repr x) = (currentWordBasis k).repr x) ↔ _
  simp only [← currentWordBasis_repr_permute, (currentWordBasis k).repr.injective.eq_iff]

/-- The actual symmetric-power module is canonically the invariant tensor space,
with symmetrization normalized by 1/k!. -/
def symmetricTensorEquiv (k : ℕ) : symmetricPower k ≃ₗ[ℂ] invariantTensors k :=
  (symmetricWordEquiv k).trans
    ((currentWordBasis k).repr.ofSubmodule' (invariantWords k)).symm

end KhanSL2.SymmetricFamily
