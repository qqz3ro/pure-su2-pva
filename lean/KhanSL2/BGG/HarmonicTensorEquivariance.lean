module

public import KhanSL2.BGG.HarmonicTensorTerms
public import KhanSL2.BGG.FreeCEEquivarianceAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG

/-- The canonical constant action agrees with the already verified relative PBW formula. -/
theorem positiveTensorAction_coefficient (p : ℕ) (x : G)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    positiveTensorAction (Coefficient p) x t = positiveTensorConstantAction p x t := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [positiveTensorAction_tmul, positiveTensorConstantAction_tmul,
      positiveUEAction_apply, coefficientAction_apply]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Harmonic coefficient inclusion is equivariant for the actual diagonal constant action. -/
theorem harmonicTensorEmbedding_constant (p : ℕ) (x : G)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    harmonicTensorEmbedding p (positiveTensorAction (Coefficient p) x t) =
      positiveTensorAction PositiveCE.Harmonic x (harmonicTensorEmbedding p t) := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [positiveTensorAction_tmul, map_add, harmonicTensorEmbedding_tmul,
      LieModuleHom.map_lie]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Harmonic coefficient projection is equivariant for the actual diagonal constant action. -/
theorem harmonicTensorProjection_constant (p : ℕ) (x : G) (t : HarmonicTensor) :
    harmonicTensorProjection p (positiveTensorAction PositiveCE.Harmonic x t) =
      positiveTensorAction (Coefficient p) x (harmonicTensorProjection p t) := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    simp only [positiveTensorAction_tmul, map_add, harmonicTensorProjection_tmul,
      LieModuleHom.map_lie]
  | add t s ht hs => simp only [map_add, ht, hs]

/-- Relative PBW identifies the canonical tensor action with constants in the current algebra. -/
theorem positiveTensorModuleEquivTerm_constant (p : ℕ) (x : G)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    positiveTensorModuleEquivTerm p (positiveTensorAction (Coefficient p) x t) =
      constGenerator x • positiveTensorModuleEquivTerm p t := by
  rw [positiveTensorModuleEquivTerm_apply, positiveTensorAction_coefficient,
    positiveTensorEquivTerm_constant]
  rfl

@[simp] theorem termHarmonicEmbedding_equiv (p : ℕ)
    (t : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    termHarmonicEmbedding p (positiveTensorModuleEquivTerm p t) = harmonicTensorEmbedding p t := by
  simp only [termHarmonicEmbedding, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

/-- The prescribed induced-term inclusion intertwines all constant currents. -/
theorem termHarmonicEmbedding_constant (p : ℕ) (x : G) (t : Term p) :
    termHarmonicEmbedding p (constGenerator x • t) =
      positiveTensorAction PositiveCE.Harmonic x (termHarmonicEmbedding p t) := by
  obtain ⟨v, rfl⟩ := (positiveTensorModuleEquivTerm p).surjective t
  rw [← positiveTensorModuleEquivTerm_constant, termHarmonicEmbedding_equiv,
    termHarmonicEmbedding_equiv, harmonicTensorEmbedding_constant]

/-- The prescribed induced-term projection intertwines all constant currents. -/
theorem termHarmonicProjection_constant (p : ℕ) (x : G) (t : HarmonicTensor) :
    termHarmonicProjection p (positiveTensorAction PositiveCE.Harmonic x t) =
      constGenerator x • termHarmonicProjection p t := by
  simp only [termHarmonicProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    harmonicTensorProjection_constant, positiveTensorModuleEquivTerm_constant]

end KhanSL2.BGG