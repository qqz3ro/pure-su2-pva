module

public import KhanSL2.PolynomialBGG.RootRing
public import KhanSL2.Collision.JFactor

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The prescribed elementary coefficient map is exactly the coefficient map
of the actual labelled characteristic polynomial. -/

noncomputable section
open Polynomial
open scoped BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- The characteristic polynomial of the actual labelled roots. -/
def labelledCharacteristic (k : ℕ) : Polynomial (RootPolynomial k) :=
  ∏ i : Fin k, (Polynomial.X - Polynomial.C (show RootPolynomial k from MvPolynomial.X i))

theorem labelledCharacteristic_monic (k : ℕ) : (labelledCharacteristic k).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)

theorem labelledCharacteristic_natDegree (k : ℕ) : (labelledCharacteristic k).natDegree = k := by
  change (∏ i : Fin k, (Polynomial.X - Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin k) ℂ))).natDegree = k
  simp [Depth.natDegree_prod_X_sub_C_X]

/-- The original R_k action is precisely the elementary coefficient map of this product. -/
theorem coeffHom_labelledCharacteristic (k : ℕ) :
    Collision.coeffHom k (labelledCharacteristic k) = rootMap k := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [Collision.coeffHom, MvPolynomial.aeval_X, Collision.elemCoord]
  rw [rootMap_X]
  change (-1 : MvPolynomial (Fin k) ℂ) ^ (j.val+1) *
    (∏ i : Fin k, (Polynomial.X - Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin k) ℂ))).coeff
      (k-1-j.val) = MvPolynomial.esymm (Fin k) ℂ (j.val+1)
  rw [Depth.coeff_prod_X_sub_C_X (Fin k) (by simp; omega), Fintype.card_fin,
    show k-(k-1-j.val)=j.val+1 by omega]
  rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- The universal polynomial becomes the actual product of linear labelled factors. -/
theorem univPoly_map_rootMap (k : ℕ) :
    (Collision.univPoly k).map (rootMap k).toRingHom = labelledCharacteristic k := by
  rw [← coeffHom_labelledCharacteristic]
  exact Collision.univPoly_map_coeffHom (labelledCharacteristic_monic k)
    (labelledCharacteristic_natDegree k)

end KhanSL2.SymmetricFamily
