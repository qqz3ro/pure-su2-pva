module

public import KhanSL2.BGG.FreeCEPBW
public import KhanSL2.BGG.FreeCEAugmentation
public import KhanSL2.BGG.PolynomialKoszulHomotopy

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual CE augmentation agrees with the scalar polynomial Koszul augmentation under PBW. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

attribute [local instance] FiniteExterior.codeOrder

private theorem augmentation_word (l : List Mode) :
    UE.augmentation ℂ positive
      (TauCeti.UniversalEnvelopingAlgebra.pbwMonomial ℂ positive positiveColorBasis l) =
        if l = [] then 1 else 0 := by
  cases l with
  | nil => simp
  | cons i l =>
    rw [TauCeti.UniversalEnvelopingAlgebra.pbwMonomial_cons, map_mul, UE.augmentation_ι, zero_mul]
    simp

/-- The ordered PBW monomial has scalar augmentation exactly when its exponent is zero. -/
theorem augmentation_pbwBasis (s : Mode →₀ ℕ) :
    UE.augmentation ℂ positive (positiveColorBasis.pbwBasis s) = if s=0 then 1 else 0 := by
  rw [Module.Basis.pbwBasis_apply, augmentation_word]
  by_cases hs : s=0
  · subst s
    simp
  · have hl : s.toMultiset.sort (· ≤ ·) ≠ [] := by
      intro h
      have hh := congrArg (fun l : List Mode => Multiset.toFinsupp (l : Multiset Mode)) h
      apply hs
      simpa only [Multiset.sort_eq, Finsupp.toMultiset_toFinsupp,
        Multiset.coe_nil, Multiset.toFinsupp_zero] using hh
    rw [if_neg hl, if_neg hs]

/-- The transported actual CE augmentation. -/
def polynomialAugmentation : PolynomialKoszul.Chain →ₗ[ℂ] ℂ :=
  augmentation.comp chainPolynomialEquiv.symm.toLinearMap

/-- PBW identifies the two specified scalar augmentations, not merely their kernels. -/
theorem polynomialAugmentation_eq : polynomialAugmentation = PolynomialKoszul.augmentation := by
  apply PolynomialKoszul.basis.ext
  rintro ⟨s,t⟩
  rw [PolynomialKoszul.augmentation_basis]
  change augmentation (chainPolynomialEquiv.symm (PolynomialKoszul.basis (s,t))) = _
  rw [PolynomialKoszul.basis_apply, chainPolynomialEquiv_symm_tmul, augmentation_tmul]
  simp only [polynomialEquiv, Module.Basis.pbwEquiv_symm_monomial, augmentation_pbwBasis]
  by_cases hs : s=0 <;> by_cases ht : t=∅ <;>
    simp [hs, ht, PolynomialKoszul.scalarIndex, scalarCoefficient, FiniteExterior.monomial]

/-- The polynomial-coordinate CE operator has the standard Koszul scalar augmentation. -/
theorem polynomialAugmentation_differential (u : PolynomialKoszul.Chain) :
    PolynomialKoszul.augmentation (polynomialDifferential u) = 0 := by
  rw [← polynomialAugmentation_eq]
  change augmentation (chainPolynomialEquiv.symm
    (chainPolynomialEquiv (differential (chainPolynomialEquiv.symm u)))) = 0
  rw [LinearEquiv.symm_apply_apply, augmentation_differential]

end KhanSL2.BGG.FreeCE
