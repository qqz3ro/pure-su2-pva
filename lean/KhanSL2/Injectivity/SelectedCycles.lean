module

public import KhanSL2.Injectivity.CartanTensorEvaluation
public import KhanSL2.Injectivity.CyclePolynomialIdentities
public import KhanSL2.Injectivity.AlternantProductSpan
public import KhanSL2.Injectivity.CycleNormalization

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.Injectivity.Cartan

open Finset MvPolynomial

def selectedNeutralIndices (r s : ℕ) : Fin r ⊕ Fin s → ℕ :=
  fun i => (finSumFinEquiv i).val

theorem neutralDeterminant_selected (r s : ℕ) :
    neutralDeterminant (selectedNeutralIndices r s) =
      (-1 : EvaluationPolynomial r s) ^ (r * s) *
        xVandermonde r s * yVandermonde r s * crossFactor r s :=
  neutralExponentDeterminant r s

theorem separatingFamily_ofFn (s : ℕ) (ns : List ℕ) {k : ℕ} (is : Fin k → ℕ)
    (p : RootPolynomial s) :
    (separatingFamily s ns (List.ofFn is)).toLinearMap p =
      orderedProduct (fun i => generator (.neutral (is i))) * (newtonFamily s ns).toLinearMap p := by
  induction k with
  | zero => simp [separatingFamily]
  | succ k ih =>
    rw [List.ofFn_succ]
    change generator (.neutral (is 0)) *
      (separatingFamily s ns (List.ofFn (Fin.tail is))).toLinearMap p = _
    rw [ih, orderedProduct_succ, mul_assoc]
    rfl

def selectedCycleChain (r s : ℕ) (e : Fin r → ℕ) (p : MvPolynomial (Fin s) ℂ) : Cochain :=
  neutralWord (selectedNeutralIndices r s) *
    (newtonFamily s (List.ofFn e)).toLinearMap (alternatingRootInput s p)

theorem selectedCycleChain_closed (r s : ℕ) (e : Fin r → ℕ)
    (p : MvPolynomial (Fin s) ℂ) (u : Cochain) :
    FiniteExterior.coefficientPairing (selectedCycleChain r s e p) (q u) = 0 := by
  have h := separatingFamily_pairing_q s (List.ofFn e)
    (List.ofFn (fun i : Fin (r + s) => i.val)) (alternatingRootInput s p) u
  rw [separatingFamily_ofFn] at h
  simpa only [selectedCycleChain, neutralWord, selectedNeutralIndices,
    Equiv.apply_symm_apply] using h

/-- The explicitly constructed closed chain realizes the exact spanning
polynomial, up to a proved nonzero scalar. -/
theorem chainPolynomial_selectedCycle (r s : ℕ) (e : Fin r → ℕ)
    (p : MvPolynomial (Fin s) ℂ) (hp : p.IsSymmetric) :
    chainPolynomial r s (selectedCycleChain r s e p) =
      selectedCycleScalar r s • cyclePolynomial r s e p := by
  rw [selectedCycleChain, chainPolynomial_newtonTensor, neutralDeterminant_selected,
    cartanNewtonDeterminant, rootAlternation_alternatingRootInput _ p hp]
  have haeval : aeval (fun i : Fin s => (X (.inr i) : EvaluationPolynomial r s)) p =
      rename Sum.inr p := by
    rw [rename_eq_aeval]
    rfl
  rw [haeval]
  change (sourceOrderingSign r s : EvaluationPolynomial r s) *
    (((-1 : EvaluationPolynomial r s) ^ (r * s) * xVandermonde r s * yVandermonde r s * crossFactor r s) *
      (((-1 : EvaluationPolynomial r s) ^ r * crossFactor r s * rename Sum.inl (TauCeti.alternant (Fin r) ℂ e)) *
        (((s.factorial : EvaluationPolynomial r s) ^ 2) * (yVandermonde r s ^ 2 * rename Sum.inr p)))) = _
  exact selectedCycleNormalization r s e p

end KhanSL2.Injectivity.Cartan
