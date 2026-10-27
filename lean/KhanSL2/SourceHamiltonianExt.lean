module

public import KhanSL2.SourceHamiltonianLeibniz

@[expose] public section

/-! A right sesquilinear superderivation is determined by its values on X and Y. -/

noncomputable section

namespace KhanSL2.Source

open LambdaPolynomial

@[simp] theorem evenPart_one : evenPart 1 = 1 := by
  simp only [evenPart_apply, map_one]
  module

@[simp] theorem oddPart_one : oddPart 1 = 0 := by
  simp [oddPart_apply]

namespace GeneralLeibniz

theorem map_one_eq_zero {M : HamiltonianAction} (hM : GeneralLeibniz M) :
    M 1 = 0 := by
  have h := hM 1 1
  have h' : M 1 = M 1 + M 1 := by
    ext n
    have hn := congrArg (fun p : LambdaPolynomial Source => p n) h
    simpa [sourceData] using hn
  apply add_left_cancel (a := M 1)
  simpa using h'.symm

theorem map_scalar_eq_zero {M : HamiltonianAction} (hM : GeneralLeibniz M) (r : ℂ) :
    M (algebraMap ℂ Source r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, hM.map_one_eq_zero, smul_zero]

/-- Equality on the two undifferentiated generators implies equality everywhere.
The two maps need only the generalized right Leibniz rule and right
sesquilinearity; no Jacobi or skew identity is assumed. -/
theorem ext {M N : HamiltonianAction}
    (hM : GeneralLeibniz M) (hN : GeneralLeibniz N)
    (hMT : ∀ a, M (translation a) = rightTranslation translation (M a))
    (hNT : ∀ a, N (translation a) = rightTranslation translation (N a))
    (hX : M (X 0) = N (X 0)) (hY : M (Y 0) = N (Y 0)) : M = N := by
  have hx : ∀ i, M (X i) = N (X i) := by
    intro i
    induction i with
    | zero => exact hX
    | succ i hi =>
      rw [← translation_X i, hMT, hNT, hi]
  have hy : ∀ i, M (Y i) = N (Y i) := by
    intro i
    induction i with
    | zero => exact hY
    | succ i hi =>
      rw [← translation_Y i, hMT, hNT, hi]
  apply LinearMap.ext
  intro a
  suffices h : M a = N a ∧ M (parity a) = N (parity a) from h.1
  induction a using inductionOn with
  | scalar r =>
    simp only [AlgHom.commutes, hM.map_scalar_eq_zero, hN.map_scalar_eq_zero,
      and_self]
  | hx i =>
    simpa only [parity_X, and_self] using hx i
  | hy i =>
    simp only [parity_Y, map_neg, hy i, and_self]
  | add a b ha hb =>
    simp only [map_add, ha.1, hb.1, ha.2, hb.2, and_self]
  | mul a b ha hb =>
    constructor
    · rw [hM, hN]
      simp only [ha.1, hb.1, parityConjugate_apply, hb.2]
    · rw [map_mul, hM, hN]
      simp only [ha.2, hb.2, parityConjugate_apply, parity_parity, hb.1]

end GeneralLeibniz

end KhanSL2.Source
