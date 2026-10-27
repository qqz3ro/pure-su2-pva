module

public import KhanSL2.BGG.RootCasimir
public import KhanSL2.BGG.PositiveEnergyCasimir

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The exact normalization between the compact color Casimir and the root
Casimir, and its restriction to actual finite CE degree-energy pieces. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG

/-- For the actual epsilon-normalized color matrices, their sum of squares is
minus one half of the root Casimir, in every complex representation. -/
theorem color_sum_lie_lie {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule G M] [LieModule ℂ G M] (u : M) :
    (∑ a : Fin 3, ⁅MatrixSL2.color a, ⁅MatrixSL2.color a, u⁆⁆) =
      (-1 / 2 : ℂ) • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f M u := by
  have hI : (-Complex.I / 2) * (-Complex.I / 2) = (-1 / 4 : ℂ) := by
    calc
      (-Complex.I / 2) * (-Complex.I / 2) = Complex.I ^ 2 / 4 := by ring
      _ = -1 / 4 := by rw [Complex.I_sq]
  simp only [Fin.sum_univ_three, MatrixSL2.color, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    TauCeti.sl2Casimir_apply,
    smul_lie, add_lie, sub_lie, lie_smul, lie_add, lie_sub,
    smul_add, smul_sub, smul_smul, hI]
  module

namespace PositiveCE

/-- The actual constant color actions have exactly the root Casimir normalization. -/
theorem colorSquares_eq_casimir (u : Cochain) :
    (∑ a : Fin 3, colorAction a (colorAction a u)) =
      (-1 / 2 : ℂ) • TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f Cochain u := by
  have hact (a : Fin 3) (v : Cochain) : ⁅MatrixSL2.color a, v⁆ = colorAction a v := by
    change ColorRoot.positiveAction (MatrixSL2.color a) v = colorAction a v
    rw [ColorRoot.positiveAction_color]
  simpa only [hact] using color_sum_lie_lie u

/-- This is the precise energy-minus-root-Casimir formula in color coordinates. -/
theorem energyCasimir_eq_energy_sub_casimir (u : Cochain) :
    energyCasimir u = energyOp u - (1 / 4 : ℂ) •
      TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f Cochain u := by
  rw [energyCasimir_apply, colorSquares_eq_casimir, smul_smul]
  module

/-- The root-normalized spectral operator on the actual finite CE piece. -/
def spectralOperator (d N : ℕ) : liePiece d N →ₗ⁅ℂ,G⁆ liePiece d N :=
  (N : ℂ) • LieModuleHom.id - (1 / 4 : ℂ) •
    TauCeti.sl2CasimirHom rootSl2Triple rootSl2Triple_top (liePiece d N)

@[simp] theorem spectralOperator_apply (d N : ℕ) (u : liePiece d N) :
    spectralOperator d N u = (N : ℂ) • u - (1 / 4 : ℂ) •
      TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f (liePiece d N) u := by
  simp [spectralOperator]

theorem coe_spectralOperator (d N : ℕ) (u : liePiece d N) :
    (spectralOperator d N u : Cochain) = (N : ℂ) • (u : Cochain) - (1 / 4 : ℂ) •
      TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f Cochain (u : Cochain) := by
  rw [spectralOperator_apply]
  change (N : ℂ) • (u : Cochain) - (1 / 4 : ℂ) •
    (TauCeti.sl2Casimir ℂ MatrixSL2.h MatrixSL2.e MatrixSL2.f (liePiece d N) u : Cochain) = _
  rw [TauCeti.coe_sl2Casimir_lieSubmodule]

/-- The ambient concrete color operator restricts exactly to the finite-piece spectral operator. -/
theorem energyCasimir_coe_piece (d N : ℕ) (u : liePiece d N) :
    energyCasimir (u : Cochain) = (spectralOperator d N u : Cochain) := by
  rw [energyCasimir_eq_energy_sub_casimir, coe_spectralOperator,
    ((mem_piece_iff_euler u d N).mp u.property).2]

/-- The finite spectral kernel in the original color-coordinate CE model. -/
def spectralKernel (d N : ℕ) : LieSubmodule ℂ G (liePiece d N) :=
  (spectralOperator d N).ker

@[simp] theorem mem_spectralKernel (d N : ℕ) (u : liePiece d N) :
    u ∈ spectralKernel d N ↔ spectralOperator d N u = 0 := Iff.rfl

end PositiveCE
namespace ColorRoot

/-- The proved coordinate comparison intertwines the actual finite spectral operators. -/
theorem liePieceEquiv_spectralOperator (d N : ℕ) (u : PositiveCE.liePiece d N) :
    liePieceEquiv d N (PositiveCE.spectralOperator d N u) =
      rootSpectralOperator d N (liePieceEquiv d N u) := by
  have hmap (x : G) (v : PositiveCE.liePiece d N) :
      liePieceEquiv d N ⁅x, v⁆ = ⁅x, liePieceEquiv d N v⁆ :=
    (liePieceEquiv d N).map_lie x v
  simp only [PositiveCE.spectralOperator_apply, rootSpectralOperator_apply,
    map_sub, map_smul, TauCeti.sl2Casimir_apply, map_add, hmap]

/-- The actual color and root spectral kernels are equivalent as sl₂ modules. -/
def spectralKernelEquivRoot (d N : ℕ) :
    PositiveCE.spectralKernel d N ≃ₗ⁅ℂ,G⁆ rootCasimirKernel d N where
  toFun u := ⟨liePieceEquiv d N u, by
    change rootSpectralOperator d N (liePieceEquiv d N u) = 0
    have hu : PositiveCE.spectralOperator d N (u : PositiveCE.liePiece d N) = 0 := u.property
    rw [← liePieceEquiv_spectralOperator, hu, map_zero]⟩
  invFun u := ⟨(liePieceEquiv d N).symm u, by
    change PositiveCE.spectralOperator d N ((liePieceEquiv d N).symm u) = 0
    apply (liePieceEquiv d N).injective
    rw [liePieceEquiv_spectralOperator, (liePieceEquiv d N).apply_symm_apply, map_zero]
    exact u.property⟩
  left_inv u := Subtype.ext ((liePieceEquiv d N).symm_apply_apply u)
  right_inv u := Subtype.ext ((liePieceEquiv d N).apply_symm_apply u)
  map_add' u v := Subtype.ext (map_add (liePieceEquiv d N)
    (u : PositiveCE.liePiece d N) (v : PositiveCE.liePiece d N))
  map_smul' r u := Subtype.ext (map_smul (liePieceEquiv d N) r (u : PositiveCE.liePiece d N))
  map_lie' {x u} := Subtype.ext ((liePieceEquiv d N).map_lie x (u : PositiveCE.liePiece d N))

end ColorRoot
end KhanSL2.BGG
