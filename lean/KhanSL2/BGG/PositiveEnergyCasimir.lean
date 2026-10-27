module

public import KhanSL2.BGG.ColorRootGrading
public import KhanSL2.BGG.PositiveCEParity
public import KhanSL2.BGG.ExteriorSecondOrderCalculus

@[expose] public section

/-! The energy-minus-Casimir operator in compact color coordinates. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- The color-action cross term in the second-order product rule. -/
def colorCross (u v : Cochain) : Cochain := ∑ a : Fin 3, colorAction a u * colorAction a v

/-- In compact coordinates, minus one quarter of the sl₂ Casimir is half the
    sum of squares of the color actions. -/
def energyCasimir : Module.End ℂ Cochain :=
  energyOp + (1/2 : ℂ) • ∑ a : Fin 3, (colorAction a).comp (colorAction a)

@[simp] theorem energyCasimir_apply (u : Cochain) :
    energyCasimir u = energyOp u + (1/2 : ℂ) • ∑ a : Fin 3, colorAction a (colorAction a u) := by
  simp only [energyCasimir, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply]

@[simp] theorem energyCasimir_one : energyCasimir 1 = 0 := by
  simp only [energyCasimir_apply, energyOp_one, colorAction_one, map_zero,
    Finset.sum_const_zero, smul_zero, add_zero]

private theorem colorSquares_generator (m : Mode) :
    (∑ a : Fin 3, colorAction a (colorAction a (FiniteExterior.generator m))) =
      (-2 : ℂ) • FiniteExterior.generator m := by
  obtain ⟨i,c⟩ := m
  simp only [colorAction_generator, map_sum, map_smul]
  fin_cases c <;> simp [Fin.sum_univ_succ, epsilon] <;> module

@[simp] theorem energyCasimir_generator (m : Mode) :
    energyCasimir (FiniteExterior.generator m) = (m.index : ℂ) • FiniteExterior.generator m := by
  rw [energyCasimir_apply, colorSquares_generator, energyOp_generator]
  simp only [smul_smul, Nat.cast_add, Nat.cast_one]
  module

/-- The product defect is exactly the color-action cross term. -/
theorem energyCasimir_mul (u v : Cochain) :
    energyCasimir (u*v) = energyCasimir u*v + u*energyCasimir v + colorCross u v := by
  simp only [energyCasimir_apply, energyOp_mul, colorAction_mul, map_add,
    Finset.sum_add_distrib, colorCross, smul_add, add_mul, mul_add,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  module

/-- The color cross term has the standard Kronecker-delta expression. -/
theorem colorCross_generator (m n : Mode) :
    colorCross (FiniteExterior.generator m) (FiniteExterior.generator n) =
      (if m.color = n.color then
        ∑ c : Fin 3, FiniteExterior.generator (⟨m.index,c⟩ : Mode) *
          FiniteExterior.generator (⟨n.index,c⟩ : Mode) else 0) -
      FiniteExterior.generator (⟨m.index,n.color⟩ : Mode) *
        FiniteExterior.generator (⟨n.index,m.color⟩ : Mode) := by
  obtain ⟨i,a⟩ := m
  obtain ⟨j,b⟩ := n
  fin_cases a <;> fin_cases b <;>
    simp only [colorCross, colorAction_generator, Fin.sum_univ_succ] <;>
    norm_num [epsilon] <;> module

theorem energyCasimir_pair (m n : Mode) :
    energyCasimir (FiniteExterior.generator m * FiniteExterior.generator n) =
      ((m.index+n.index : ℕ) : ℂ) •
        (FiniteExterior.generator m * FiniteExterior.generator n) +
      colorCross (FiniteExterior.generator m) (FiniteExterior.generator n) := by
  rw [energyCasimir_mul, energyCasimir_generator, energyCasimir_generator]
  simp only [smul_mul_assoc, mul_smul_comm, Nat.cast_add, add_smul]


/-- The RHS is second order because it is an even derivation plus squares of
    parity-preserving even derivations. -/
theorem energyCasimir_secondOrder : HasSecondOrderLeibniz energyCasimir := by
  have hE : HasEvenLeibniz energyOp := energyOp_mul
  have hL (a : Fin 3) : HasEvenLeibniz (colorAction a) := colorAction_mul a
  have hs (S : Finset (Fin 3)) :
      HasSecondOrderLeibniz (∑ a∈S, (colorAction a).comp (colorAction a)) := by
    induction S using Finset.induction_on with
    | empty =>
      intro a u v
      simp [generatorDefect_apply]
    | @insert a S ha ih =>
      rw [Finset.sum_insert ha]
      exact (secondOrder_even_even _ _ (hL a) (hL a)
        (colorAction_parity a) (colorAction_parity a)).add ih
  exact hE.secondOrder.add ((hs Finset.univ).smul (1/2))

end KhanSL2.BGG.PositiveCE
