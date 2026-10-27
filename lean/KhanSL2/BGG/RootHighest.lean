module

public import KhanSL2.BGG.RootCartan

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Explicit raising/lowering operators and the minimum-energy highest wedge. -/

noncomputable section
namespace KhanSL2.BGG

private theorem lie_e_h : ⁅MatrixSL2.e, MatrixSL2.h⁆ = (-2 : ℂ) • MatrixSL2.e := by
  rw [← lie_skew MatrixSL2.e MatrixSL2.h, G.lie_h_e]
  simp

private theorem lie_f_e : ⁅MatrixSL2.f, MatrixSL2.e⁆ = -MatrixSL2.h := by
  rw [← lie_skew MatrixSL2.f MatrixSL2.e, G.lie_e_f]

private theorem lie_f_h : ⁅MatrixSL2.f, MatrixSL2.h⁆ = (2 : ℂ) • MatrixSL2.f := by
  rw [← lie_skew MatrixSL2.f MatrixSL2.h, G.lie_h_f]
  simp

@[simp] theorem rootExteriorAction_e_generator_zero (n : ℕ) :
    rootExteriorAction MatrixSL2.e (FiniteExterior.generator (n, 0)) = 0 := by
  rw [← rootCurrentGenerator_positiveMode_rootBasis n 0, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode, rootBasis_zero, LieRing.lie_self, map_zero, map_zero]

@[simp] theorem rootExteriorAction_e_generator_one (n : ℕ) :
    rootExteriorAction MatrixSL2.e (FiniteExterior.generator (n, 1)) =
      (-2 : ℂ) • FiniteExterior.generator (n, 0) := by
  rw [← rootCurrentGenerator_positiveMode_rootBasis n 1, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode, rootBasis_one, lie_e_h, map_smul, map_smul]
  rw [← rootBasis_zero, rootCurrentGenerator_positiveMode_rootBasis]

@[simp] theorem rootExteriorAction_e_generator_two (n : ℕ) :
    rootExteriorAction MatrixSL2.e (FiniteExterior.generator (n, 2)) =
      FiniteExterior.generator (n, 1) := by
  rw [← rootCurrentGenerator_positiveMode_rootBasis n 2, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode, rootBasis_two, G.lie_e_f]
  rw [← rootBasis_one, rootCurrentGenerator_positiveMode_rootBasis]

@[simp] theorem rootExteriorAction_f_generator_zero (n : ℕ) :
    rootExteriorAction MatrixSL2.f (FiniteExterior.generator (n, 0)) =
      -FiniteExterior.generator (n, 1) := by
  rw [← rootCurrentGenerator_positiveMode_rootBasis n 0, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode, rootBasis_zero, lie_f_e, map_neg, map_neg]
  rw [← rootBasis_one, rootCurrentGenerator_positiveMode_rootBasis]

@[simp] theorem rootExteriorAction_f_generator_one (n : ℕ) :
    rootExteriorAction MatrixSL2.f (FiniteExterior.generator (n, 1)) =
      (2 : ℂ) • FiniteExterior.generator (n, 2) := by
  rw [← rootCurrentGenerator_positiveMode_rootBasis n 1, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode, rootBasis_one, lie_f_h, map_smul, map_smul]
  rw [← rootBasis_two, rootCurrentGenerator_positiveMode_rootBasis]

@[simp] theorem rootExteriorAction_f_generator_two (n : ℕ) :
    rootExteriorAction MatrixSL2.f (FiniteExterior.generator (n, 2)) = 0 := by
  rw [← rootCurrentGenerator_positiveMode_rootBasis n 2, rootExteriorAction_currentGenerator,
    positiveAdjoint_positiveMode, rootBasis_two, LieRing.lie_self, map_zero, map_zero]

/-- The distinguished highest wedge belongs to its expected degree-energy component. -/
theorem rootHighest_mem_piece (j : ℕ) :
    FiniteExterior.monomial (RootSupport.highest j).toFinset ∈
      rootExteriorPiece j (triangular j) := by
  rw [rootMonomial_mem_piece, RootSupport.card_toFinset, rootMonomialEnergy_toFinset]
  simp

/-- The distinguished wedge has actual Cartan eigenvalue `2j`. -/
theorem rootHighest_h (j : ℕ) :
    rootExteriorAction MatrixSL2.h (FiniteExterior.monomial (RootSupport.highest j).toFinset) =
      (2 * (j : ℂ)) • FiniteExterior.monomial (RootSupport.highest j).toFinset := by
  rw [rootExteriorAction_h_monomial, rootMonomialWeight_toFinset, RootSupport.highest_weight]
  simp

/-- The distinguished minimum-energy wedge is a genuine highest-weight vector. -/
theorem rootHighest_e (j : ℕ) :
    rootExteriorAction MatrixSL2.e (FiniteExterior.monomial (RootSupport.highest j).toFinset) = 0 := by
  have hzero (i : RootMode) (hi : i ∈ (RootSupport.highest j).toFinset) :
      rootExteriorAction MatrixSL2.e (FiniteExterior.generator i) = 0 := by
    obtain ⟨n, a⟩ := i
    have hh : (n, a) ∈ (Finset.range j).map (rootColorEmbedding 0) := by
      simpa [RootSupport.highest, RootSupport.toFinset] using hi
    obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hh
    have ha0 := congrArg (fun k : RootMode => k.2) hm
    have ha : a = 0 := ha0.symm
    subst a
    exact rootExteriorAction_e_generator_zero n
  change FiniteExterior.extendDerivation FiniteExterior.GeneratorOrder.code
    (fun i => FiniteExterior.generatorLinear (rootModeAction MatrixSL2.e (Finsupp.single i 1)))
    (FiniteExterior.monomial (RootSupport.highest j).toFinset) = 0
  rw [FiniteExterior.extendDerivation_monomial]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← rootExteriorAction_generator, hzero i hi]
  simp

end KhanSL2.BGG