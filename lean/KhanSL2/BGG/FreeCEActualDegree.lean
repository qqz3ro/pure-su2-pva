module

public import KhanSL2.BGG.FreeCEExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The verified CE exactness theorem in the actual base-changed exterior-degree modules. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

/-- PBW degree coordinates describe precisely the actual base change of exterior degree. -/
theorem mem_baseChangedDegree_iff (p : ℕ) (u : Chain) :
    u ∈ (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p}).baseChange PositiveEnveloping ↔
      chainPolynomialEquiv u ∈ PolynomialKoszul.degreePiece p := by
  constructor
  · intro hu
    obtain ⟨t, rfl⟩ := hu
    induction t using TensorProduct.inductionOn with
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, chainPolynomialEquiv_tmul,
        PolynomialKoszul.mem_degreePiece_iff, PolynomialKoszul.exteriorDegree_tmul]
      have hv : PositiveCE.degreeOp (v : Cochain) = (p : ℂ) • (v : Cochain) :=
        (FiniteExterior.euler_degree_eq_smul_iff p (v : Cochain)).mpr v.property
      simp only [Submodule.subtype_apply]
      rw [hv, TensorProduct.tmul_smul]
    | add t s ht hs => simpa only [map_add] using (PolynomialKoszul.degreePiece p).add_mem ht hs
  · intro hu
    change ∀ b ∈ (PolynomialKoszul.basis.repr (chainPolynomialEquiv u)).support, b.2.card = p at hu
    rw [← chainPolynomialEquiv.symm_apply_apply u,
      PolynomialKoszul.eq_sum_basis (chainPolynomialEquiv u), map_sum]
    apply Submodule.sum_mem
    rintro ⟨s,t⟩ hb
    rw [map_smul, PolynomialKoszul.basis_apply, chainPolynomialEquiv_symm_tmul,
      TensorProduct.smul_tmul']
    exact Submodule.tmul_mem_baseChange_of_mem _
      (Finsupp.single_mem_supported ℂ 1 (hu (s,t) hb))

/-- Every augmented CE cycle has a primitive in the actual next exterior-degree module. -/
theorem augmented_exactness_baseChangedDegree (p : ℕ) (u : Chain)
    (hp : u ∈ (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p}).baseChange PositiveEnveloping)
    (hu : differential u = 0) (hε : augmentation u = 0) :
    ∃ v ∈ (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p + 1}).baseChange PositiveEnveloping,
      differential v = u := by
  obtain ⟨v, hvP, hv⟩ := augmented_exactness_degree p u ((mem_baseChangedDegree_iff p u).mp hp) hu hε
  exact ⟨v, (mem_baseChangedDegree_iff (p + 1) v).mpr hvP, hv⟩

/-- Positive exterior degree automatically has zero augmentation. -/
theorem augmentation_eq_zero_of_baseChangedDegree (p : ℕ) (u : Chain)
    (hp : u ∈ (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p + 1}).baseChange PositiveEnveloping) :
    augmentation u = 0 := by
  have h := PolynomialKoszul.augmentation_eq_zero_of_positive_degree
    ((mem_baseChangedDegree_iff (p + 1) u).mp hp)
  rw [← polynomialAugmentation_eq] at h
  change augmentation (chainPolynomialEquiv.symm (chainPolynomialEquiv u)) = 0 at h
  simpa only [LinearEquiv.symm_apply_apply] using h

/-- Exactness at every positive exterior degree in the actual base-changed CE modules. -/
theorem exactness_positive_degree (p : ℕ) (u : Chain)
    (hp : u ∈ (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p + 1}).baseChange PositiveEnveloping)
    (hu : differential u = 0) :
    ∃ v ∈ (Finsupp.supported ℂ ℂ {s : Finset Mode | s.card = p + 2}).baseChange PositiveEnveloping,
      differential v = u :=
  augmented_exactness_baseChangedDegree (p + 1) u hp hu
    (augmentation_eq_zero_of_baseChangedDegree p u hp)

end KhanSL2.BGG.FreeCE
