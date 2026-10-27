module

public import KhanSL2.Injectivity.CartanTensor
public import KhanSL2.Injectivity.RootCyclePairing

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.Injectivity

open Finset

theorem det_sum_rows {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (S : ι → Finset ℕ) (t : ι → ℕ → R) (v : ℕ → ι → R) :
    Matrix.det (fun i k => ∑ j ∈ S i, t i j * v j k) =
      ∑ j ∈ Fintype.piFinset S, (∏ i, t i (j i)) * Matrix.det (fun i k => v (j i) k) := by
  have h := (Matrix.detRowAlternating (R := R) (n := ι)).toMultilinearMap.map_sum_finset
    (fun i j => t i j • v j) S
  change Matrix.det (fun i => ∑ j ∈ S i, t i j • v j) = _ at h
  have hl : (fun i => ∑ j ∈ S i, t i j • v j) =
      (fun i k => ∑ j ∈ S i, t i j * v j k) := by
    funext i k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hl] at h
  rw [h]
  apply sum_congr rfl
  intro j _hj
  exact Matrix.det_mul_column _ _

theorem cartanModePairing_mapCoefficients {P R : Type*} [CommRing P] [CommRing R]
    (f : P →+* R) (θ : ℕ →₀ P) (z : R) :
    cartanModePairing z (mapCartanCoefficients f θ) =
      ∑ j ∈ θ.support, f (θ j) * ((j : R) * z ^ (j - 1)) := by
  simp only [cartanModePairing, Finsupp.linearCombination_apply, mapCartanCoefficients,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finsupp.sum_mapRange_index (by intro; simp)]
  rfl

namespace Cartan

open MvPolynomial

def neutralWord {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) : Cochain :=
  orderedProduct (fun i => generator (.neutral (a (finSumFinEquiv.symm i))))

def neutralDeterminant {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) : EvaluationPolynomial r s :=
  Matrix.det (fun i j : Fin r ⊕ Fin s => X j ^ a i)

def diagonalRootEvaluation (r s : ℕ) : RootPolynomial s →ₐ[ℂ] EvaluationPolynomial r s :=
  rootPointEvaluation (fun i : Fin s => X (.inr i)) 1 1

def thetaPairingMatrix {r s : ℕ} (θ : Fin r → ℕ →₀ RootPolynomial s) :
    Matrix (Fin r) (Fin r) (EvaluationPolynomial r s) :=
  fun i k => ∑ j ∈ (θ i).support,
    diagonalRootEvaluation r s (θ i j) * ((j : EvaluationPolynomial r s) * X (.inl k) ^ (j - 1))

theorem chainPolynomial_cartanTensor {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ)
    (θ : Fin r → ℕ →₀ RootPolynomial s) (p : RootPolynomial s)
    (hzero : ∀ i, θ i 0 = 0)
    (hdiag : ∀ (e f : Equiv.Perm (Fin s)) i j,
      rootPointEvaluation (fun k : Fin s => (X (.inr k) : EvaluationPolynomial r s)) e f (θ i j) =
        diagonalRootEvaluation r s (θ i j)) :
    chainPolynomial r s (neutralWord a * cartanTensor s θ p) =
      (sourceOrderingSign r s : EvaluationPolynomial r s) *
        (neutralDeterminant a * (Matrix.det (thetaPairingMatrix θ) *
          rootAlternation (fun i : Fin s => X (.inr i)) p)) := by
  rw [cartanTensor_expansion, mul_sum, map_sum]
  have hterm (j : Fin r → ℕ) (hj : j ∈ Fintype.piFinset (fun i => (θ i).support)) :
      chainPolynomial r s (neutralWord a *
        (orderedProduct (fun i => generator (.cartan (j i - 1))) *
          rootEncode s ((∏ i, θ i (j i)) * p))) =
      (sourceOrderingSign r s : EvaluationPolynomial r s) *
        (neutralDeterminant a *
          (((∏ i, diagonalRootEvaluation r s (θ i (j i))) *
            Matrix.det (fun i k : Fin r => (j i : EvaluationPolynomial r s) * X (.inl k) ^ (j i - 1))) *
            rootAlternation (fun i : Fin s => X (.inr i)) p)) := by
    change chainPolynomial r s (prefixedRootEncode a (fun i => j i - 1) ((∏ i, θ i (j i)) * p)) = _
    rw [chainPolynomial_prefixedRootEncode,
      rootAlternation_mul_constant _ _ _ (∏ i, diagonalRootEvaluation r s (θ i (j i)))]
    · have hjpos (i : Fin r) : j i - 1 + 1 = j i := by
        have hmem := Fintype.mem_piFinset.mp hj i
        have hn : j i ≠ 0 := by
          intro h
          rw [h] at hmem
          exact (Finsupp.mem_support_iff.mp hmem) (hzero i)
        omega
      simp only [hjpos]
      change _ = (sourceOrderingSign r s : EvaluationPolynomial r s) *
        (Matrix.det (fun i j : Fin r ⊕ Fin s => X j ^ a i) * _)
      ring
    · intro e f
      simp only [map_prod, hdiag]
  rw [sum_congr rfl hterm]
  simp only [← mul_sum, ← sum_mul]
  unfold thetaPairingMatrix
  rw [det_sum_rows]

theorem thetaPairingMatrix_rootTheta (r s : ℕ) (e : Fin r → ℕ) :
    thetaPairingMatrix (fun i => rootTheta s (e i)) =
      fun i k => cartanModePairing (X (.inl k) : EvaluationPolynomial r s)
        (rootCycle (fun j : Fin s => X (.inr j)) (fun j : Fin s => X (.inr j)) (s + 1 + e i)) := by
  funext i k
  dsimp only [thetaPairingMatrix]
  have hpair := cartanModePairing_mapCoefficients (diagonalRootEvaluation r s).toRingHom
    (rootTheta s (e i)) (X (.inl k))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hpair
  rw [← hpair]
  congr 1
  apply Finsupp.ext
  intro j
  exact rootPointEvaluation_rootCycle
    (fun j : Fin s => (X (.inr j) : EvaluationPolynomial r s)) 1 1 (s + 1 + e i) j

theorem chainPolynomial_newtonTensor (r s : ℕ) (a : Fin r ⊕ Fin s → ℕ)
    (e : Fin r → ℕ) (p : RootPolynomial s) :
    chainPolynomial r s (neutralWord a * (newtonFamily s (List.ofFn e)).toLinearMap p) =
      (sourceOrderingSign r s : EvaluationPolynomial r s) *
        (neutralDeterminant a *
          (Matrix.det (fun i k => cartanModePairing (X (.inl k) : EvaluationPolynomial r s)
            (rootCycle (fun j : Fin s => X (.inr j)) (fun j : Fin s => X (.inr j)) (s + 1 + e i))) *
            rootAlternation (fun i : Fin s => X (.inr i)) p)) := by
  rw [← cartanTensor_eq_newtonFamily]
  rw [chainPolynomial_cartanTensor a _ p (fun i => rootTheta_zero s (e i))]
  · rw [thetaPairingMatrix_rootTheta]
  · intro f g i j
    rw [rootTheta, rootPointEvaluation_rootCycle]
    exact (rootPointEvaluation_rootCycle
      (fun j : Fin s => (X (.inr j) : EvaluationPolynomial r s)) 1 1 (s + 1 + e i) j).symm

end Cartan
end KhanSL2.Injectivity
