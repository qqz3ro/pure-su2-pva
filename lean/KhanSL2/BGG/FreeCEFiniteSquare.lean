module

public import KhanSL2.BGG.FreeCEOperators

@[expose] public section
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE
open PositiveCE FiniteExterior

/-- The finite bracket cutoff, extended linearly over the enveloping algebra. -/
def finiteBracket (S : Finset Mode) : Module.End PositiveEnveloping Chain :=
  (-(1/2:ℂ)) • ∑ m∈S, ∑ n∈S, ∑ a : Fin 3,
    KhanSL2.epsilon a m.color n.color • bracketTerm m n a

@[simp] theorem finiteBracket_tmul (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain) :
    finiteBracket S (u ⊗ₜ[ℂ] ω) = u ⊗ₜ[ℂ] finiteBoundary S ω := by
  simp only [finiteBracket, LinearMap.smul_apply, LinearMap.sum_apply, bracketTerm_tmul,
    finiteBoundary_apply, TensorProduct.tmul_smul, TensorProduct.tmul_sum, boundaryTerm_apply]

/-- The coefficient commutator left after pairing the two action summands. -/
def coefficientCorrection (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain) : Chain :=
  ∑ m∈S, ∑ n∈S, ∑ a : Fin 3, KhanSL2.epsilon a m.color n.color •
    ((u * ueGenerator (mergeMode m n a)) ⊗ₜ[ℂ] contract n (contract m ω))

private theorem actionTerm_pair_sum (m n : Mode) (u : PositiveEnveloping) (ω : Cochain) :
    actionTerm m (actionTerm n (u ⊗ₜ[ℂ] ω)) + actionTerm n (actionTerm m (u ⊗ₜ[ℂ] ω)) =
      ∑ a : Fin 3, KhanSL2.epsilon a m.color n.color •
        ((u * ueGenerator (mergeMode m n a)) ⊗ₜ[ℂ] contract n (contract m ω)) := by
  rw [add_comm, actionTerm_anticommutator n m, ueGenerator_commutator]
  simp only [Finset.mul_sum, mul_smul_comm, TensorProduct.sum_tmul,
    TensorProduct.smul_tmul']

/-- The action-only square is half the coefficient correction. -/
theorem finiteAction_square (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain) :
    finiteAction S (finiteAction S (u ⊗ₜ[ℂ] ω)) =
      (1/2:ℂ) • coefficientCorrection S u ω := by
  have hsum :
      (∑ m∈S, ∑ n∈S, (actionTerm m (actionTerm n (u ⊗ₜ[ℂ] ω)) +
        actionTerm n (actionTerm m (u ⊗ₜ[ℂ] ω)))) = coefficientCorrection S u ω := by
    simp only [actionTerm_pair_sum, coefficientCorrection]
  have hswap : (∑ m∈S, ∑ n∈S, actionTerm n (actionTerm m (u ⊗ₜ[ℂ] ω))) =
      ∑ m∈S, ∑ n∈S, actionTerm m (actionTerm n (u ⊗ₜ[ℂ] ω)) := Finset.sum_comm
  simp only [Finset.sum_add_distrib] at hsum
  rw [hswap] at hsum
  have hval : finiteAction S (finiteAction S (u ⊗ₜ[ℂ] ω)) =
      ∑ m∈S, ∑ n∈S, actionTerm m (actionTerm n (u ⊗ₜ[ℂ] ω)) := by
    simp only [finiteAction, LinearMap.sum_apply, map_sum]
    exact hswap
  rw [hval]
  rw [← hsum]
  module

private theorem finiteAction_bracketTerm (T : Finset Mode) (m n : Mode) (a : Fin 3)
    (ha : mergeMode m n a ∈ T) (u : PositiveEnveloping) (ω : Cochain) :
    finiteAction T (bracketTerm m n a (u ⊗ₜ[ℂ] ω)) +
      bracketTerm m n a (finiteAction T (u ⊗ₜ[ℂ] ω)) =
      (u * ueGenerator (mergeMode m n a)) ⊗ₜ[ℂ] contract n (contract m ω) := by
  simp only [finiteAction, LinearMap.sum_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  simp only [actionTerm_bracketTerm, Finset.sum_ite_eq', ha, ite_true]

/-- The mixed action/bracket anticommutator cancels the action-only square. -/
theorem finiteAction_bracket (S T : Finset Mode)
    (hmerge : ∀ m∈S, ∀ n∈S, ∀ a : Fin 3, mergeMode m n a ∈ T)
    (u : PositiveEnveloping) (ω : Cochain) :
    finiteAction T (finiteBracket S (u ⊗ₜ[ℂ] ω)) +
      finiteBracket S (finiteAction T (u ⊗ₜ[ℂ] ω)) =
      -(1/2:ℂ) • coefficientCorrection S u ω := by
  simp only [finiteBracket, LinearMap.smul_apply, LinearMap.sum_apply, map_sum,
    LinearMap.map_smul_of_tower]
  rw [← smul_add]
  simp only [← Finset.sum_add_distrib, ← smul_add]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteAction_bracketTerm T m n a (hmerge m hm n hn a)]

end KhanSL2.BGG.FreeCE