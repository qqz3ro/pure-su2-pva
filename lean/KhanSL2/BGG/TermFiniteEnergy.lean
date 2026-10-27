module

public import KhanSL2.BGG.PositiveUEFiniteEnergy
public import KhanSL2.BGG.TermPBWGrading
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG

/-- The intrinsic tensor energy piece is spanned by tensors from the corresponding
positive enveloping energy and the finite coefficient representation. -/
theorem positiveTensorPiece_le_range_energyTensor (p : ℕ) (n : ℤ) :
    positiveTensorPiece p n ≤ LinearMap.range
      (TensorProduct.map (positiveUEPiece (n - generatorEnergy p)).subtype
        (LinearMap.id : Coefficient p →ₗ[ℂ] Coefficient p)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨l, v, hl, rfl⟩
  have he : WordGrading.degree positiveEnergy l = n - generatorEnergy p := by omega
  have hw : WordGrading.word positiveUEGenerator l ∈ positiveUEPiece (n - generatorEnergy p) := by
    rw [← he]
    exact WordGrading.word_mem_piece positiveUEGenerator positiveEnergy l
  exact ⟨(⟨WordGrading.word positiveUEGenerator l, hw⟩ : positiveUEPiece (n - generatorEnergy p)) ⊗ₜ[ℂ] v,
    rfl⟩

/-- Every intrinsic shifted tensor piece is finite-dimensional. -/
instance finiteDimensional_positiveTensorPiece (p : ℕ) (n : ℤ) :
    FiniteDimensional ℂ (positiveTensorPiece p n) := by
  let f := TensorProduct.map (positiveUEPiece (n - generatorEnergy p)).subtype
    (LinearMap.id : Coefficient p →ₗ[ℂ] Coefficient p)
  have : FiniteDimensional ℂ ((positiveUEPiece (n - generatorEnergy p)) ⊗[ℂ] Coefficient p) := inferInstance
  have : FiniteDimensional ℂ (LinearMap.range f) := inferInstance
  let g : positiveTensorPiece p n →ₗ[ℂ] LinearMap.range f :=
    Submodule.inclusion (positiveTensorPiece_le_range_energyTensor p n)
  exact FiniteDimensional.of_injective (K := ℂ) (V := positiveTensorPiece p n)
    (V₂ := LinearMap.range f) g (Submodule.inclusion_injective _)

/-- Relative PBW restricts to an equivalence of the actual energy pieces. -/
def positiveEnergyTensorEquivTermPiece (p : ℕ) (n : ℤ) :
    positiveTensorPiece p n ≃ₗ[ℂ] termPiece p n :=
  (positiveTensorEquivTerm p).ofSubmodules (positiveTensorPiece p n) (termPiece p n) (by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact positiveTensorEquivTerm_degree p hv
    · intro hu
      refine ⟨(positiveTensorEquivTerm p).symm u, ?_, (positiveTensorEquivTerm p).apply_symm_apply u⟩
      apply (positiveTensorEquivTerm_mem_iff p n _).mp
      simpa only [LinearEquiv.apply_symm_apply] using hu)

/-- Every actual quotient BGG energy piece is finite-dimensional, in every degree
and at every integer energy, including the vanishing negative and below-shift pieces. -/
instance finiteDimensional_termPiece (p : ℕ) (n : ℤ) : FiniteDimensional ℂ (termPiece p n) := by
  exact FiniteDimensional.of_surjective (K := ℂ) (V := positiveTensorPiece p n)
    (V₂ := termPiece p n) (positiveEnergyTensorEquivTermPiece p n).toLinearMap
    (positiveEnergyTensorEquivTermPiece p n).surjective

/-- The triangular generator shift is at least the homological degree. -/
theorem degree_le_generatorEnergy (p : ℕ) : p ≤ generatorEnergy p := by
  cases p with
  | zero => simp
  | succ p =>
    unfold generatorEnergy
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    exact Nat.mul_le_mul_left (p+1) (by omega)

/-- A fixed energy contains only finitely many homological terms. -/
theorem termPiece_eq_bot_of_degree_gt_energy (p : ℕ) (n : ℤ) (hp : n.toNat < p) :
    termPiece p n = ⊥ := by
  apply termPiece_below
  have h := degree_le_generatorEnergy p
  omega

theorem finite_nonzero_termPiece_degrees (n : ℤ) : {p : ℕ | termPiece p n ≠ ⊥}.Finite := by
  apply (Finset.range (n.toNat+1)).finite_toSet.subset
  intro p hp
  change p ∈ Finset.range (n.toNat+1)
  rw [Finset.mem_range]
  by_contra h
  exact hp (termPiece_eq_bot_of_degree_gt_energy p n (by omega))
end KhanSL2.BGG
