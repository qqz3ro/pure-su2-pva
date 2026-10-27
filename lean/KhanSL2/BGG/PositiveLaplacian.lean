module

public import KhanSL2.BGG.PositiveLaplacianOrder
public import KhanSL2.BGG.PositiveLaplacianPairs
public import KhanSL2.BGG.PositiveEnergyCasimir

@[expose] public section

/-! The concrete positive-current Laplacian identity, proved from its finite
boundary formula, its values on words of length at most two, and second-order
extensionality. -/

noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- The actual CE Laplacian is physical energy plus half the compact color Casimir. -/
theorem laplacian_eq_energyCasimir : laplacian = energyCasimir := by
  apply secondOrder_ext laplacian energyCasimir laplacian_secondOrder energyCasimir_secondOrder
  · rw [laplacian_one, energyCasimir_one]
  · intro m
    rw [laplacian_generator, energyCasimir_generator]
  · intro m n
    rw [laplacian_pair, energyCasimir_pair, colorCross_generator]
    abel

/-- The energy/Casimir formula on every finite positive-current cochain. -/
theorem laplacian_eq_energy_colorSquares (u : Cochain) :
    d (boundary u) + boundary (d u) =
      energyOp u + (1/2 : ℂ) • ∑ a : Fin 3, colorAction a (colorAction a u) := by
  rw [← laplacian_apply, laplacian_eq_energyCasimir, energyCasimir_apply]

/-- Its full product defect is the color-action cross term. -/
theorem laplacian_mul (u v : Cochain) :
    laplacian (u*v) = laplacian u*v + u*laplacian v + colorCross u v := by
  rw [laplacian_eq_energyCasimir, energyCasimir_mul]

end KhanSL2.BGG.PositiveCE
