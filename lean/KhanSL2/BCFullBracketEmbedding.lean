module

public import KhanSL2.BCFullEmbedding
public import KhanSL2.BCFullBracketDefinition
public import KhanSL2.BCBracketDefinition
public import KhanSL2.PVAMap

@[expose] public section

/-! Adjoining zero ghosts preserves the original concrete `bc` bracket. -/

noncomputable section

namespace KhanSL2

open LambdaPolynomial

theorem fullPosition_map (m : Mode) (s : ExteriorMonomial) :
    FullBC.fullPosition (.inr m) (s.map modeInclusion) = position m s :=
  FiniteExterior.position_map Mode.code FullMode.code modeInclusion FullMode.code_inr_lt m s

theorem fullInclusion_mulRight (p : LambdaPolynomial Cochain) (u : Cochain) :
    coefficientMap fullInclusion.toLinearMap (mulRight cochainData p u) =
      mulRight fullData (coefficientMap fullInclusion.toLinearMap p) (fullInclusion u) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [mulRight_add, map_add, hp, hq]
  | single n a =>
    simpa only [mulRight_single, coefficientMap_single, cochainData, fullData, wedge, fullWedge,
      fullWedgeLinear, FiniteExterior.wedge,
      AlgHom.toLinearMap_apply] using
        congrArg (Finsupp.single n) (fullInclusion_wedge a u)

theorem fullInclusion_generatorActionMonomial (m : Mode) (s : ExteriorMonomial) :
    coefficientMap fullInclusion.toLinearMap (BC.generatorActionMonomial m s) =
      FullBC.generatorActionMonomial (.inr m) (s.map modeInclusion) := by
  simp only [BC.generatorActionMonomial, FullBC.generatorActionMonomial,
    map_sum, map_smul, coefficientMap_single, AlgHom.toLinearMap_apply, fullInclusion_single,
    BC.monomial, FullBC.monomial, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro n _
  change _ = ((-1 : ℂ) ^ FullBC.fullPosition (.inr n) (s.map modeInclusion)) •
    Finsupp.single (FullMode.order (.inr m) + FullMode.order (.inr n))
      (FullBC.kernelCoefficient (.inr m) (.inr n) •
        Finsupp.single ((s.map modeInclusion).erase (.inr n)) 1)
  rw [fullPosition_map, FullBC.kernelCoefficient_inr]
  simp only [FullMode.order, map_smul, BC.monomial, fullInclusion_single]
  rw [Finset.map_erase]
  rfl

theorem fullInclusion_monomialGeneratorAction (s : ExteriorMonomial) (m : Mode) :
    coefficientMap fullInclusion.toLinearMap (BC.monomialGeneratorAction s m) =
      FullBC.monomialGeneratorAction (s.map modeInclusion) (.inr m) := by
  simp only [BC.monomialGeneratorAction, FullBC.monomialGeneratorAction,
    map_smul, Finset.card_map]
  rw [coefficientMap_skew fullInclusion.toLinearMap translation fullTranslation
    fullInclusion_translation, fullInclusion_generatorActionMonomial]

theorem fullInclusion_monomialBracket (s t : ExteriorMonomial) :
    coefficientMap fullInclusion.toLinearMap (BC.monomialBracket s t) =
      FullBC.monomialBracket (s.map modeInclusion) (t.map modeInclusion) := by
  simp only [BC.monomialBracket, FullBC.monomialBracket, map_sum, map_smul,
    fullInclusion_mulRight, fullInclusion_monomialGeneratorAction, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro m _
  change _ = ((-1 : ℂ) ^ FullBC.fullPosition (.inr m) (t.map modeInclusion)) •
    mulRight fullData (FullBC.monomialGeneratorAction (s.map modeInclusion) (.inr m))
      (FullBC.monomial ((t.map modeInclusion).erase (.inr m)))
  rw [fullPosition_map]
  simp only [BC.monomial, FullBC.monomial, fullInclusion_single, Finset.map_erase]
  rfl

theorem fullInclusion_bracket_poly (a b : Cochain) :
    coefficientMap fullInclusion.toLinearMap (BC.bracket a b) =
      FullBC.bracket (fullInclusion a) (fullInclusion b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | single s r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [map_add, hb, hc]
    | single t u =>
      simp only [BC.bracket_single, FullBC.bracket_single, map_smul,
        fullInclusion_single, fullInclusion_monomialBracket]

theorem fullInclusion_bracket (a b : Cochain) (n : ℕ) :
    fullInclusion (BC.bracket a b n) =
      FullBC.bracket (fullInclusion a) (fullInclusion b) n :=
  congrArg (fun p : LambdaPolynomial FullCochain => p n) (fullInclusion_bracket_poly a b)

def fullInclusionPVAMap : PVAMap cochainData BC.bracket fullData FullBC.bracket where
  linear := fullInclusion.toLinearMap
  map_one := fullInclusion_one
  map_mul := fullInclusion_wedge
  map_translation := fullInclusion_translation
  map_bracket := fullInclusion_bracket

end KhanSL2
