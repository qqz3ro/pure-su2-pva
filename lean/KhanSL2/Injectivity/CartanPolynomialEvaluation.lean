module

public import KhanSL2.Injectivity.CartanRestriction
public import KhanSL2.Injectivity.ExteriorPolynomialEvaluation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-! The finite generating polynomial of a Cartan chain, in source-factor order. -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity.Cartan

open MvPolynomial

abbrev SourceSlot (r s : ℕ) := (Fin r × Fin 2) ⊕ (Fin s × Fin 3)
abbrev EvaluationPolynomial (r s : ℕ) := MvPolynomial (Fin r ⊕ Fin s) ℂ

/-- Source slots occur in the order `(neutral,Cartan)` for each X, followed by
`(neutral,plus,minus)` for each Y. -/
def sourceSlotEquiv (r s : ℕ) : SourceSlot r s ≃ Fin (r * 2 + s * 3) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

/-- One-particle generating weights. Cartan modes use their predecessor index,
so `cartan j` pairs with `(j+1) z^j`. -/
def sourceSlotWeight (r s : ℕ) : Mode → SourceSlot r s → EvaluationPolynomial r s
  | .neutral j, .inl (i, k) => if k = 0 then X (.inl i) ^ j else 0
  | .neutral j, .inr (a, k) => if k = 0 then X (.inr a) ^ j else 0
  | .cartan j, .inl (i, k) =>
      if k = 1 then ((j + 1 : ℕ) : EvaluationPolynomial r s) * X (.inl i) ^ j else 0
  | .cartan _, .inr _ => 0
  | .plus _, .inl _ => 0
  | .plus j, .inr (a, k) => if k = 1 then X (.inr a) ^ j else 0
  | .minus _, .inl _ => 0
  | .minus j, .inr (a, k) => if k = 2 then X (.inr a) ^ j else 0

def slotWeight (r s : ℕ) (m : Mode) (j : Fin (r * 2 + s * 3)) : EvaluationPolynomial r s :=
  sourceSlotWeight r s m ((sourceSlotEquiv r s).symm j)

@[simp] theorem slotWeight_sourceSlotEquiv (r s : ℕ) (m : Mode) (j : SourceSlot r s) :
    slotWeight r s m (sourceSlotEquiv r s j) = sourceSlotWeight r s m j := by
  simp [slotWeight]

/-- The finite generating polynomial of a chain. Its source-Taylor normalization
has the additional scalar `(-2)^s`, coming from the Y representative. -/
def chainPolynomial (r s : ℕ) : Cochain →ₗ[ℂ] EvaluationPolynomial r s :=
  FiniteExterior.determinantEvaluation (r * 2 + s * 3) (slotWeight r s)

theorem chainPolynomial_orderedProduct (r s : ℕ) (a : Fin (r * 2 + s * 3) → Mode) :
    chainPolynomial r s (orderedProduct (fun i => generator (a i))) =
      Matrix.det (fun i j => slotWeight r s (a i) j) :=
  FiniteExterior.determinantEvaluation_orderedProduct _ _ _

theorem chainPolynomial_orderedProduct_other (r s n : ℕ) (a : Fin n → Mode)
    (h : n ≠ r * 2 + s * 3) :
    chainPolynomial r s (orderedProduct (fun i => generator (a i))) = 0 :=
  FiniteExterior.determinantEvaluation_orderedProduct_other _ _ _ _ h

end KhanSL2.Injectivity.Cartan
