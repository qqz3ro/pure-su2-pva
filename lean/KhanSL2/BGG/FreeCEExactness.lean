module

public import KhanSL2.BGG.FreeCELowering
public import KhanSL2.BGG.FreeCESquareZero
public import KhanSL2.BGG.FreeCEAugmentationModule
public import KhanSL2.BGG.FilteredCorrection

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Augmented exactness of the actual free Chevalley--Eilenberg complex, proved by PBW and Koszul. -/

noncomputable section
namespace KhanSL2.BGG.FreeCE

open PolynomialKoszul

@[simp] theorem polynomialDifferential_square_zero (u : PolynomialKoszul.Chain) :
    polynomialDifferential (polynomialDifferential u) = 0 := by
  change chainPolynomialEquiv (differential (chainPolynomialEquiv.symm
    (chainPolynomialEquiv (differential (chainPolynomialEquiv.symm u))))) = 0
  rw [LinearEquiv.symm_apply_apply, differential_square_zero, map_zero]

/-- Every augmented cycle has an actual primitive, with no exactness hypothesis. -/
theorem polynomial_augmented_exactness (u : PolynomialKoszul.Chain)
    (hu : polynomialDifferential u = 0) (hε : PolynomialKoszul.augmentation u = 0) :
    ∃ v, polynomialDifferential v = u :=
  FilteredCorrection.exists_primitive PolynomialKoszul.d polynomialDifferential homotopy
    PolynomialKoszul.augmentation inclusion filtration filtration_zero filtration_exhaustive
    (fun _ _ hx => homotopy_mem_filtration hx) polynomialPerturbation_lowers
    contraction_apply polynomialDifferential_square_zero polynomialAugmentation_differential u hu hε

/-- The primitive can be chosen in precisely the next exterior degree. -/
theorem polynomial_augmented_exactness_degree (p : ℕ) (u : PolynomialKoszul.Chain)
    (hp : u ∈ degreePiece p) (hu : polynomialDifferential u = 0)
    (hε : PolynomialKoszul.augmentation u = 0) :
    ∃ v ∈ degreePiece (p + 1), polynomialDifferential v = u :=
  FilteredCorrection.exists_primitive_mem PolynomialKoszul.d polynomialDifferential homotopy
    PolynomialKoszul.augmentation inclusion filtration filtration_zero filtration_exhaustive
    (fun _ _ hx => homotopy_mem_filtration hx) polynomialPerturbation_lowers
    contraction_apply polynomialDifferential_square_zero polynomialAugmentation_differential
    (degreePiece p) (degreePiece (p + 1))
    (fun _ hx => homotopy_mem_degreePiece hx)
    (fun _ hx => polynomialDifferential_mem_degreePiece hx) u hp hu hε

/-- PBW intertwines the original actual CE operator and its polynomial-coordinate operator. -/
theorem polynomialDifferential_chainPolynomialEquiv (u : Chain) :
    polynomialDifferential (chainPolynomialEquiv u) = chainPolynomialEquiv (differential u) := by
  change chainPolynomialEquiv (differential (chainPolynomialEquiv.symm (chainPolynomialEquiv u))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The original augmented free CE complex is exact; this proves, rather than assumes, its acyclicity. -/
theorem augmented_exactness (u : Chain) (hu : differential u = 0) (hε : augmentation u = 0) :
    ∃ v, differential v = u := by
  have hp : polynomialDifferential (chainPolynomialEquiv u) = 0 := by
    rw [polynomialDifferential_chainPolynomialEquiv, hu, map_zero]
  have ha : PolynomialKoszul.augmentation (chainPolynomialEquiv u) = 0 := by
    rw [← polynomialAugmentation_eq]
    change augmentation (chainPolynomialEquiv.symm (chainPolynomialEquiv u)) = 0
    rw [LinearEquiv.symm_apply_apply, hε]
  obtain ⟨v, hv⟩ := polynomial_augmented_exactness (chainPolynomialEquiv u) hp ha
  refine ⟨chainPolynomialEquiv.symm v, chainPolynomialEquiv.injective ?_⟩
  exact hv

/-- The exactness interface for transfer by an A-linear HPL contraction. -/
theorem augmented_exactness_module (u : Chain)
    (hu : differential u = 0) (hε : augmentationModule u = 0) :
    ∃ v, differential v = u := augmented_exactness u hu hε

/-- The degreewise augmented exactness theorem on the actual free CE module. -/
theorem augmented_exactness_degree (p : ℕ) (u : Chain)
    (hp : chainPolynomialEquiv u ∈ degreePiece p) (hu : differential u = 0)
    (hε : augmentation u = 0) :
    ∃ v, chainPolynomialEquiv v ∈ degreePiece (p + 1) ∧ differential v = u := by
  have hd : polynomialDifferential (chainPolynomialEquiv u) = 0 := by
    rw [polynomialDifferential_chainPolynomialEquiv, hu, map_zero]
  have ha : PolynomialKoszul.augmentation (chainPolynomialEquiv u) = 0 := by
    rw [← polynomialAugmentation_eq]
    change augmentation (chainPolynomialEquiv.symm (chainPolynomialEquiv u)) = 0
    rw [LinearEquiv.symm_apply_apply, hε]
  obtain ⟨v, hvP, hv⟩ := polynomial_augmented_exactness_degree p (chainPolynomialEquiv u) hp hd ha
  refine ⟨chainPolynomialEquiv.symm v, ?_, chainPolynomialEquiv.injective hv⟩
  rwa [LinearEquiv.apply_symm_apply]

end KhanSL2.BGG.FreeCE
