module

public import KhanSL2.BGG.TermResolutionEquivariance
public import KhanSL2.BGG.FreeCEAugmentationEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.TermResolution

/-- The actual transferred augmentation is equivariant for positive currents. -/
theorem augmentation_positive_smul (u : PositiveEnveloping) (v : Term 0) :
    augmentation (u • v) = UE.augmentation ℂ positive u * augmentation v := by
  change FreeCE.augmentation (PositiveTransfer.contraction.incl (termHarmonicEmbedding 0 (u • v))) = _
  rw [map_smul, map_smul, FreeCE.augmentation_smul, FreeCE.scalar_positive_smul]
  rfl

/-- Constants act trivially on the value of the constructed augmentation. -/
theorem augmentation_constant (x : G) (v : Term 0) :
    augmentation (constGenerator x • v) = 0 := by
  change FreeCE.augmentation (PositiveTransfer.contraction.incl
    (termHarmonicEmbedding 0 (constGenerator x • v))) = 0
  rw [termHarmonicEmbedding_constant, PositiveTransfer.contraction_incl_constantAction,
    FreeCE.augmentation_constantAction]

/-- Every actual current generator acts trivially after augmentation. -/
theorem augmentation_generator (x : Current) (v : Term 0) :
    augmentation ((UniversalEnvelopingAlgebra.ι ℂ x : Enveloping) • v) = 0 := by
  let u : positive := ⟨x - constant (evalZero x), sub_constant_mem_positive x⟩
  have hx : (UniversalEnvelopingAlgebra.ι ℂ x : Enveloping) =
      positiveFactor (UniversalEnvelopingAlgebra.ι ℂ u) + constGenerator (evalZero x) := by
    rw [positiveFactor_iota]
    change UniversalEnvelopingAlgebra.ι ℂ x =
      UniversalEnvelopingAlgebra.ι ℂ (x - constant (evalZero x)) +
        UniversalEnvelopingAlgebra.ι ℂ (constant (evalZero x))
    rw [← map_add, sub_add_cancel]
  rw [hx, add_smul, map_add, augmentation_constant, add_zero]
  change augmentation ((UniversalEnvelopingAlgebra.ι ℂ u : PositiveEnveloping) • v) = 0
  rw [augmentation_positive_smul, UE.augmentation_ι, zero_mul]

/-- The augmentation is a morphism to the actual trivial full-current representation. -/
theorem augmentation_smul (a : Enveloping) (v : Term 0) :
    augmentation (a • v) = UE.augmentation ℂ Current a * augmentation v := by
  induction a using UE.induction ℂ Current generalizing v with
  | scalar r =>
    rw [algebraMap_smul, map_smul, AlgHom.commutes]
    rfl
  | generator x => rw [augmentation_generator, UE.augmentation_ι, zero_mul]
  | add a b ha hb => rw [add_smul, map_add, ha, hb, map_add, add_mul]
  | mul a b ha hb => rw [mul_smul, ha, hb, map_mul, mul_assoc]

end KhanSL2.BGG.TermResolution