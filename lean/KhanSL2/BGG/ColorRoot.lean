module

public import KhanSL2.BGG.PositiveCE
public import KhanSL2.BGG.RootHighest
public import KhanSL2.ColorBasis

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Explicit mode-wise color/root comparison for positive-current CE exterior algebra. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG.ColorRoot

/-- Insert a three-coordinate vector in one root mode. -/
def rootCoordinatesAt (n : ℕ) : (Fin 3 → ℂ) →ₗ[ℂ] RootExterior where
  toFun v := ∑ a : Fin 3, v a • FiniteExterior.generator (n, a)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum, smul_smul]

/-- Insert a three-coordinate vector in one color mode. -/
def colorCoordinatesAt (n : ℕ) : (Fin 3 → ℂ) →ₗ[ℂ] PositiveCE.Cochain where
  toFun v := ∑ a : Fin 3, v a • FiniteExterior.generator (⟨n, a⟩ : PositiveCE.Mode)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.smul_sum, smul_smul]

def rootAt (n : ℕ) : G →ₗ[ℂ] RootExterior :=
  (rootCoordinatesAt n).comp rootEquiv.symm.toLinearMap

def colorAt (n : ℕ) : G →ₗ[ℂ] PositiveCE.Cochain :=
  (colorCoordinatesAt n).comp MatrixSL2.colorEquiv.symm.toLinearMap

theorem rootAt_apply (n : ℕ) (x : G) :
    rootAt n x = ∑ a : Fin 3, rootEquiv.symm x a • FiniteExterior.generator (n, a) := rfl

theorem colorAt_apply (n : ℕ) (x : G) :
    colorAt n x = ∑ a : Fin 3, MatrixSL2.colorEquiv.symm x a •
      FiniteExterior.generator (⟨n, a⟩ : PositiveCE.Mode) := rfl

@[simp] theorem rootAt_rootBasis (n : ℕ) (a : Fin 3) :
    rootAt n (rootBasis a) = FiniteExterior.generator (n, a) := by
  simp [rootAt, rootCoordinatesAt, rootBasis, Pi.basisFun_apply]

private theorem colorEquiv_basisFun (a : Fin 3) :
    MatrixSL2.colorEquiv (Pi.basisFun ℂ (Fin 3) a) = MatrixSL2.color a := by
  fin_cases a <;> simp [MatrixSL2.colorEquiv, Pi.basisFun_apply]

@[simp] theorem colorAt_color (n : ℕ) (a : Fin 3) :
    colorAt n (MatrixSL2.color a) = FiniteExterior.generator (⟨n, a⟩ : PositiveCE.Mode) := by
  rw [← colorEquiv_basisFun a]
  simp [colorAt, colorCoordinatesAt, Pi.basisFun_apply]

theorem parity_rootAt (n : ℕ) (x : G) :
    FiniteExterior.parityLinear (rootAt n x) = -rootAt n x := by
  simp [rootAt_apply, map_sum, Finset.sum_neg_distrib]

theorem parity_colorAt (n : ℕ) (x : G) :
    FiniteExterior.parityLinear (colorAt n x) = -colorAt n x := by
  simp [colorAt_apply, map_sum, Finset.sum_neg_distrib]

/-- Each color generator maps to its specified root coordinates, at the same mode. -/
def toRoot : PositiveCE.Cochain →ₐ[ℂ] RootExterior :=
  FiniteExterior.substituteOdd
    (fun m : PositiveCE.Mode => rootAt m.index (MatrixSL2.color m.color))
    (fun m => parity_rootAt m.index (MatrixSL2.color m.color))

/-- Each root generator maps to its specified color coordinates, at the same mode. -/
def toColor : RootExterior →ₐ[ℂ] PositiveCE.Cochain :=
  FiniteExterior.substituteOdd
    (fun i : RootMode => colorAt i.1 (rootBasis i.2))
    (fun i => parity_colorAt i.1 (rootBasis i.2))

@[simp] theorem toRoot_generator (n : ℕ) (a : Fin 3) :
    toRoot (FiniteExterior.generator (⟨n, a⟩ : PositiveCE.Mode)) = rootAt n (MatrixSL2.color a) := by
  exact FiniteExterior.substituteOdd_generator (α := PositiveCE.Mode) (β := RootMode)
    (fun m => rootAt m.index (MatrixSL2.color m.color))
    (fun m => parity_rootAt m.index (MatrixSL2.color m.color)) ⟨n, a⟩

@[simp] theorem toColor_generator (n : ℕ) (a : Fin 3) :
    toColor (FiniteExterior.generator (n, a)) = colorAt n (rootBasis a) := by
  exact FiniteExterior.substituteOdd_generator (α := RootMode) (β := PositiveCE.Mode)
    (fun i => colorAt i.1 (rootBasis i.2))
    (fun i => parity_colorAt i.1 (rootBasis i.2)) (n, a)

private theorem color_decompose (x : G) :
    (∑ a : Fin 3, MatrixSL2.colorEquiv.symm x a • MatrixSL2.color a) = x := by
  rw [← MatrixSL2.colorEquiv_apply]
  exact MatrixSL2.colorEquiv.apply_symm_apply x

private theorem root_decompose (x : G) :
    (∑ a : Fin 3, rootEquiv.symm x a • rootBasis a) = x := by
  simp only [Fin.sum_univ_three, rootBasis_zero, rootBasis_one, rootBasis_two]
  exact rootEquiv.apply_symm_apply x

@[simp] theorem toRoot_colorAt (n : ℕ) (x : G) : toRoot (colorAt n x) = rootAt n x := by
  rw [colorAt_apply, map_sum]
  simp only [map_smul, toRoot_generator]
  simp only [← map_smul, ← map_sum, color_decompose]

@[simp] theorem toColor_rootAt (n : ℕ) (x : G) : toColor (rootAt n x) = colorAt n x := by
  rw [rootAt_apply, map_sum]
  simp only [map_smul, toColor_generator]
  simp only [← map_smul, ← map_sum, root_decompose]

theorem toColor_comp_toRoot : toColor.comp toRoot = AlgHom.id ℂ PositiveCE.Cochain := by
  apply FiniteExterior.algHom_ext
  intro m
  obtain ⟨n, a⟩ := m
  simp

theorem toRoot_comp_toColor : toRoot.comp toColor = AlgHom.id ℂ RootExterior := by
  apply FiniteExterior.algHom_ext
  intro i
  obtain ⟨n, a⟩ := i
  simp

/-- The requested explicit algebra equivalence between color and root positive-current coordinates. -/
def equiv : PositiveCE.Cochain ≃ₐ[ℂ] RootExterior :=
  AlgEquiv.ofAlgHom toRoot toColor toRoot_comp_toColor toColor_comp_toRoot

@[simp] theorem equiv_apply (u : PositiveCE.Cochain) : equiv u = toRoot u := rfl
@[simp] theorem equiv_symm_apply (u : RootExterior) : equiv.symm u = toColor u := rfl

/-- Root coordinates agree with the proved actual-positive-current embedding. -/
theorem rootAt_eq (n : ℕ) : rootAt n = rootCurrentGenerator.comp (positiveMode n) := by
  apply rootBasis.ext
  intro a
  simp

theorem rootExteriorAction_rootAt (x y : G) (n : ℕ) :
    rootExteriorAction x (rootAt n y) = rootAt n ⁅x, y⁆ := by
  simp only [rootAt_eq, LinearMap.comp_apply, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode]

end KhanSL2.BGG.ColorRoot