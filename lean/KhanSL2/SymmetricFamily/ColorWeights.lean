module

public import KhanSL2.SymmetricFamily.CurrentSlots
public import KhanSL2.BGGBridge.TopWeights

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Explicit even Cartan bounds and the unique top color word in labelled current tensors. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG BGG BGGBridge

/-- Half of the Cartan weight of an actual labelled root-color word. -/
def colorWordHalfWeight {k : ℕ} (c : Fin k → Fin 3) : ℤ :=
  ∑ i : Fin k, coefficientHalfWeight (c i)

theorem colorWordHalfWeight_bounds {k : ℕ} (c : Fin k → Fin 3) :
    -(k : ℤ) ≤ colorWordHalfWeight c ∧ colorWordHalfWeight c ≤ (k : ℤ) := by
  constructor
  · calc
      -(k : ℤ) = ∑ _i : Fin k, (-1 : ℤ) := by simp
      _ ≤ colorWordHalfWeight c :=
        Finset.sum_le_sum (fun i _ => (coefficientHalfWeight_bounds (c i)).1)
  · calc
      colorWordHalfWeight c ≤ ∑ _i : Fin k, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => (coefficientHalfWeight_bounds (c i)).2)
      _ = (k : ℤ) := by simp

/-- Maximal weight forces every root-color slot to be e. -/
theorem colorWordHalfWeight_eq_top_iff {k : ℕ} (c : Fin k → Fin 3) :
    colorWordHalfWeight c = (k : ℤ) ↔ c = fun _ => 0 := by
  constructor
  · intro h
    have hs : ∑ i : Fin k, (1-coefficientHalfWeight (c i)) = 0 := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      change (k : ℤ) - colorWordHalfWeight c = 0
      rw [h, sub_self]
    have hn (i : Fin k) (_ : i ∈ Finset.univ) : 0 ≤ 1-coefficientHalfWeight (c i) :=
      sub_nonneg.mpr (coefficientHalfWeight_bounds (c i)).2
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs
    funext i
    apply (coefficientHalfWeight_eq_one_iff (c i)).mp
    exact (sub_eq_zero.mp (hz i (Finset.mem_univ i))).symm
  · intro h
    rw [h]
    simp [colorWordHalfWeight, coefficientHalfWeight]

theorem colorWordHalfWeight_lt_top {k : ℕ} (c : Fin k → Fin 3)
    (hc : c ≠ fun _ => 0) : colorWordHalfWeight c < (k : ℤ) :=
  lt_of_le_of_ne (colorWordHalfWeight_bounds c).2
    (fun h => hc ((colorWordHalfWeight_eq_top_iff c).mp h))

private theorem colorDeriv_diagonal (k : ℕ) (D : Module.End ℂ BGG.G)
    (w : Fin 3 → ℂ) (hD : ∀ a, D (rootBasis a) = w a • rootBasis a)
    (c : Fin k → Fin 3) :
    colorDeriv k D (Pi.basisFun ℂ (Fin k → Fin 3) c) =
      (∑ i : Fin k, w (c i)) • Pi.basisFun ℂ (Fin k → Fin 3) c := by
  rw [colorDeriv_basis, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hD, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply, Function.update_eq_self]

/-- The genuine constant Cartan action is diagonal with even eigenvalues in the stated interval. -/
theorem colorCartan_basis (k : ℕ) (c : Fin k → Fin 3) :
    colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)
      (Pi.basisFun ℂ (Fin k → Fin 3) c) =
      (2 * (colorWordHalfWeight c : ℂ)) • Pi.basisFun ℂ (Fin k → Fin 3) c := by
  rw [colorDeriv_diagonal k _ rootWeight (fun a => lie_h_rootBasis a)]
  congr 1
  simp only [rootWeight_eq_twice, ← Finset.mul_sum, colorWordHalfWeight, Int.cast_sum]

end KhanSL2.SymmetricFamily
