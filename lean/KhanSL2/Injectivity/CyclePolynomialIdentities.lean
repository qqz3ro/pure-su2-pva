module

public import KhanSL2.Injectivity.VandermondeAppend
public import KhanSL2.Injectivity.AlternantProductSpan
public import KhanSL2.Injectivity.RootCyclePairing

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

namespace KhanSL2.Injectivity.Cartan

open Finset MvPolynomial

theorem neutralExponentDeterminant (r s : ℕ) :
    Matrix.det (fun i j : Fin r ⊕ Fin s =>
      (X j : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (finSumFinEquiv i).val) =
      (-1 : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (r * s) *
        xVandermonde r s * yVandermonde r s * crossFactor r s := by
  have hmat : (fun i j : Fin r ⊕ Fin s =>
      (X i : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (finSumFinEquiv j).val) =
      (Matrix.vandermonde (fun i : Fin (r + s) =>
        (X (finSumFinEquiv.symm i) : MvPolynomial (Fin r ⊕ Fin s) ℂ))).submatrix
          finSumFinEquiv finSumFinEquiv := by
    ext i j
    simp [Matrix.vandermonde_apply]
  have hw : (fun i : Fin (r + s) =>
      (X (finSumFinEquiv.symm i) : MvPolynomial (Fin r ⊕ Fin s) ℂ)) =
      Fin.append (fun i : Fin r => X (.inl i)) (fun i : Fin s => X (.inr i)) := by
    funext i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  rw [← Matrix.det_transpose]
  change Matrix.det (fun i j : Fin r ⊕ Fin s =>
    (X i : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (finSumFinEquiv j).val) = _
  rw [hmat, Matrix.det_submatrix_equiv_self, hw, neutral_vandermonde]

theorem cartanNewtonDeterminant (r s : ℕ) (e : Fin r → ℕ) :
    Matrix.det (fun i k => cartanModePairing (X (.inl k) : MvPolynomial (Fin r ⊕ Fin s) ℂ)
      (rootCycle (fun j : Fin s => X (.inr j)) (fun j : Fin s => X (.inr j)) (s + 1 + e i))) =
      (-1 : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ r * crossFactor r s *
        rename Sum.inl (TauCeti.alternant (Fin r) ℂ e) := by
  rw [← Matrix.det_transpose]
  have h := rootCycle_pairing_det (fun j : Fin s => (X (.inr j) : MvPolynomial (Fin r ⊕ Fin s) ℂ))
    (fun i : Fin r => X (.inl i)) e
  simp only [Fintype.card_fin] at h
  rw [show Matrix.transpose (fun i k => cartanModePairing (X (.inl k) : MvPolynomial (Fin r ⊕ Fin s) ℂ)
      (rootCycle (fun j : Fin s => X (.inr j)) (fun j : Fin s => X (.inr j)) (s + 1 + e i))) =
      (fun k i => cartanModePairing (X (.inl k) : MvPolynomial (Fin r ⊕ Fin s) ℂ)
        (rootCycle (fun j : Fin s => X (.inr j)) (fun j : Fin s => X (.inr j)) (s + 1 + e i))) from rfl,
    h]
  have halt : Matrix.det (fun i j : Fin r => (X (.inl i) : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ e j) =
      rename Sum.inl (TauCeti.alternant (Fin r) ℂ e) := by
    rw [TauCeti.alternant_def, AlgHom.map_det]
    congr 1
    ext i j
    simp
  rw [halt]
  congr 1
  simp only [prod_neg, card_univ, Fintype.card_fin, crossFactor]

end KhanSL2.Injectivity.Cartan
