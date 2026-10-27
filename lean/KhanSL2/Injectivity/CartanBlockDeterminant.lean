module

public import KhanSL2.Injectivity.CartanPolynomialEvaluation
public import KhanSL2.Injectivity.RootPolynomialEncoding
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.Injectivity

theorem orderedProduct_finCongr {A : Type*} [Ring A] {m n : ℕ} (h : m = n)
    (f : Fin n → A) : orderedProduct (fun i => f (finCongr h i)) = orderedProduct f := by
  subst n
  rfl

theorem orderedProduct_sumEquiv {A : Type*} [Ring A] {m n : ℕ}
    (f : Fin m ⊕ Fin n → A) :
    orderedProduct (fun i => f (finSumFinEquiv.symm i)) =
      orderedProduct (fun i => f (.inl i)) * orderedProduct (fun i => f (.inr i)) := by
  have he : (fun i => f (finSumFinEquiv.symm i)) =
      Fin.append (fun i => f (.inl i)) (fun i => f (.inr i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  rw [he, orderedProduct_append]

namespace Cartan

/-- Slot order for the block determinant: neutral, Cartan, plus, minus. -/
abbrev GroupedSlot (r s : ℕ) := (Fin r ⊕ Fin s) ⊕ (Fin r ⊕ (Fin s ⊕ Fin s))

def groupedRawEquiv (r s : ℕ) : GroupedSlot r s ≃ Fin ((r + s) + (r + (s + s))) :=
  (Equiv.sumCongr finSumFinEquiv
    ((Equiv.sumCongr (Equiv.refl (Fin r)) finSumFinEquiv).trans finSumFinEquiv)).trans
      finSumFinEquiv

def groupedIndexEquiv (r s : ℕ) : GroupedSlot r s ≃ Fin (r * 2 + s * 3) :=
  (groupedRawEquiv r s).trans (finCongr (by omega))

def groupedSourceEquiv (r s : ℕ) : GroupedSlot r s ≃ SourceSlot r s where
  toFun
    | .inl (.inl i) => .inl (i, 0)
    | .inl (.inr a) => .inr (a, 0)
    | .inr (.inl i) => .inl (i, 1)
    | .inr (.inr (.inl a)) => .inr (a, 1)
    | .inr (.inr (.inr a)) => .inr (a, 2)
  invFun
    | .inl (i, k) => if k = 0 then .inl (.inl i) else .inr (.inl i)
    | .inr (a, k) => if k = 0 then .inl (.inr a) else
        if k = 1 then .inr (.inr (.inl a)) else .inr (.inr (.inr a))
  left_inv := by
    rintro ((i | a) | (i | (a | a))) <;> rfl
  right_inv := by
    rintro (⟨i, k⟩ | ⟨a, k⟩) <;> fin_cases k <;> rfl

def groupedColumnEquiv (r s : ℕ) : GroupedSlot r s ≃ Fin (r * 2 + s * 3) :=
  (groupedSourceEquiv r s).trans (sourceSlotEquiv r s)

def sourceOrderingSign (r s : ℕ) : ℤˣ :=
  Equiv.Perm.sign ((groupedColumnEquiv r s).trans (groupedIndexEquiv r s).symm)

def groupedMode {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) (b : Fin r → ℕ)
    (c d : Fin s → ℕ) : GroupedSlot r s → Mode :=
  Sum.elim (fun i => .neutral (a i))
    (Sum.elim (fun i => .cartan (b i))
      (Sum.elim (fun i => .plus (c i)) (fun i => .minus (d i))))

def fullWord {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) (b : Fin r → ℕ)
    (c d : Fin s → ℕ) : Cochain :=
  orderedProduct (fun i => generator (.neutral (a (finSumFinEquiv.symm i)))) *
    (orderedProduct (fun i => generator (.cartan (b i))) * rootWord c d)

theorem fullWord_orderedProduct {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) (b : Fin r → ℕ)
    (c d : Fin s → ℕ) :
    fullWord a b c d = orderedProduct (fun i =>
      generator (groupedMode a b c d ((groupedIndexEquiv r s).symm i))) := by
  unfold groupedIndexEquiv
  simp only [Equiv.symm_trans_apply, finCongr_symm]
  rw [orderedProduct_finCongr (by omega : r * 2 + s * 3 = (r + s) + (r + (s + s)))
    (fun j => generator (groupedMode a b c d ((groupedRawEquiv r s).symm j)))]
  unfold groupedRawEquiv
  simp only [Equiv.symm_trans_apply]
  rw [orderedProduct_sumEquiv (m := r + s) (n := r + (s + s)) (fun j =>
    generator (groupedMode a b c d
      ((Equiv.sumCongr finSumFinEquiv
        ((Equiv.sumCongr (Equiv.refl (Fin r)) finSumFinEquiv).trans finSumFinEquiv)).symm j)))]
  simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.symm_trans_apply, Equiv.refl_symm, Equiv.refl_apply, groupedMode, Sum.elim_inl, Sum.elim_inr]
  rw [orderedProduct_sumEquiv (m := r) (n := s + s) (fun j =>
    generator (Sum.elim (fun i => Mode.cartan (b i))
      (Sum.elim (fun i => Mode.plus (c i)) (fun i => Mode.minus (d i)))
        (Sum.map (Equiv.refl (Fin r)) finSumFinEquiv.symm j)))]
  simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Equiv.refl_symm, Equiv.refl_apply, Sum.elim_inl, Sum.elim_inr]
  rw [orderedProduct_sumEquiv (m := s) (n := s) (fun j =>
    generator (Sum.elim (fun i => Mode.plus (c i)) (fun i => Mode.minus (d i)) j))]
  rfl

theorem chainPolynomial_grouped {r s : ℕ} (a : GroupedSlot r s → Mode) :
    chainPolynomial r s (orderedProduct (fun i =>
      generator (a ((groupedIndexEquiv r s).symm i)))) =
      (sourceOrderingSign r s : EvaluationPolynomial r s) *
        Matrix.det (fun i j => sourceSlotWeight r s (a i) (groupedSourceEquiv r s j)) := by
  rw [chainPolynomial_orderedProduct]
  let M : Matrix (GroupedSlot r s) (GroupedSlot r s) (EvaluationPolynomial r s) :=
    fun i j => slotWeight r s (a i) (groupedIndexEquiv r s j)
  have hdet : Matrix.det (fun i j => slotWeight r s (a ((groupedIndexEquiv r s).symm i)) j) =
      Matrix.det M := by
    have hm : M.submatrix (groupedIndexEquiv r s).symm (groupedIndexEquiv r s).symm =
        (fun i j => slotWeight r s (a ((groupedIndexEquiv r s).symm i)) j) := by
      apply Matrix.ext
      intro i j
      change slotWeight r s (a ((groupedIndexEquiv r s).symm i))
        ((groupedIndexEquiv r s) ((groupedIndexEquiv r s).symm j)) = _
      rw [Equiv.apply_symm_apply]
    have h := Matrix.det_submatrix_equiv_self (groupedIndexEquiv r s).symm M
    rw [hm] at h
    exact h
  rw [hdet]
  let e := (groupedColumnEquiv r s).trans (groupedIndexEquiv r s).symm
  have he := Matrix.det_permute' e M
  have hmatrix : M.submatrix id e =
      fun i j => sourceSlotWeight r s (a i) (groupedSourceEquiv r s j) := by
    ext i j
    simp [M, e, groupedColumnEquiv, slotWeight]
  rw [hmatrix] at he
  have hs : (sourceOrderingSign r s : EvaluationPolynomial r s) *
      (sourceOrderingSign r s : EvaluationPolynomial r s) = 1 := by
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  rw [he, ← mul_assoc, show (Equiv.Perm.sign e : EvaluationPolynomial r s) =
    (sourceOrderingSign r s : EvaluationPolynomial r s) from rfl, hs, one_mul]

/-- The generating polynomial of a four-color word is a product of four
determinants, with the exact source-slot permutation sign retained. -/
theorem chainPolynomial_fullWord {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) (b : Fin r → ℕ)
    (c d : Fin s → ℕ) :
    chainPolynomial r s (fullWord a b c d) =
      (sourceOrderingSign r s : EvaluationPolynomial r s) *
      (Matrix.det (fun i j : Fin r ⊕ Fin s => MvPolynomial.X j ^ a i) *
        (Matrix.det (fun i j : Fin r => ((b i + 1 : ℕ) : EvaluationPolynomial r s) *
          MvPolynomial.X (.inl j) ^ b i) *
          (Matrix.det (fun i j : Fin s => MvPolynomial.X (.inr j) ^ c i) *
            Matrix.det (fun i j : Fin s => MvPolynomial.X (.inr j) ^ d i)))) := by
  rw [fullWord_orderedProduct, chainPolynomial_grouped]
  congr 1
  have hm : (fun i j => sourceSlotWeight r s (groupedMode a b c d i)
      (groupedSourceEquiv r s j)) =
      Matrix.fromBlocks (fun i j : Fin r ⊕ Fin s => MvPolynomial.X j ^ a i) 0 0
        (Matrix.fromBlocks (fun i j : Fin r => ((b i + 1 : ℕ) : EvaluationPolynomial r s) *
          MvPolynomial.X (.inl j) ^ b i) 0 0
          (Matrix.fromBlocks (fun i j : Fin s => MvPolynomial.X (.inr j) ^ c i) 0 0
            (fun i j : Fin s => MvPolynomial.X (.inr j) ^ d i))) := by
    funext i j
    rcases i with (i | i) | i | i | i <;>
      rcases j with (j | j) | j | j | j <;>
      simp [groupedMode, groupedSourceEquiv, sourceSlotWeight, Matrix.fromBlocks]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁]

end Cartan
end KhanSL2.Injectivity
