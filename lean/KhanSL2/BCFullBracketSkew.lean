module

public import KhanSL2.BCFullBracketDefinition
public import KhanSL2.BCSkewCalculus
public import KhanSL2.BCFullCE
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-! Super-skew of the explicit exterior Wick formula. -/

noncomputable section

namespace KhanSL2.FullBC

open LambdaPolynomial BC.PolynomialCalculus

private theorem mulRight_smul (D : DifferentialData FullCochain) (r : ℂ)
    (p : LambdaPolynomial FullCochain) (b : FullCochain) :
    mulRight D (r • p) b = r • mulRight D p b :=
  (mulRightLinear D b).map_smul r p

private theorem mulRight_sum {ι : Type*} (D : DifferentialData FullCochain)
    (s : Finset ι) (f : ι → LambdaPolynomial FullCochain) (b : FullCochain) :
    mulRight D (∑ i ∈ s, f i) b = ∑ i ∈ s, mulRight D (f i) b :=
  map_sum (mulRightLinear D b) f s

private theorem skew_eq_K (p : LambdaPolynomial FullCochain) :
    minusVariableMinusTranslation fullTranslation p = K fullData p :=
  (K_apply fullData p).symm

def wickTerm (s t : FullExteriorMonomial) (m n : FullMode) : LambdaPolynomial FullCochain :=
  mulRight fullData
    (K fullData (Finsupp.single (m.order + n.order) (monomial (s.erase m))))
    (monomial (t.erase n))

theorem monomialBracket_eq_sum (s t : FullExteriorMonomial) :
    monomialBracket s t =
      ∑ n ∈ t, ∑ m ∈ s,
        (((-1 : ℂ) ^ fullPosition n t) * (-1 : ℂ) ^ (s.card + 1) *
          (-1 : ℂ) ^ fullPosition m s * kernelCoefficient n m) • wickTerm s t m n := by
  simp only [monomialBracket, monomialGeneratorAction, generatorActionMonomial,
    skew_eq_K, ← Finsupp.smul_single,
    map_sum, map_smul, Finset.smul_sum, mulRight_sum, mulRight_smul, smul_smul]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [Nat.add_comm n.order m.order]
  simp only [wickTerm, mul_assoc]

theorem K_wickTerm (hT : ∀ a b, fullTranslation (fullWedge a b) =
      fullWedge (fullTranslation a) b + fullWedge a (fullTranslation b))
    (hcomm : ∀ (s t : FullExteriorMonomial) (k : ℕ),
      fullWedge (monomial s) ((fullTranslation ^ k) (monomial t)) =
        (-1 : ℂ) ^ (s.card * t.card) •
          fullWedge ((fullTranslation ^ k) (monomial t)) (monomial s))
    (s t : FullExteriorMonomial) (m n : FullMode) :
    K fullData (wickTerm t s n m) =
      ((-1 : ℂ) ^ (m.order + n.order) *
        (-1 : ℂ) ^ ((t.erase n).card * (s.erase m).card)) • wickTerm s t m n := by
  change R fullData (monomial (s.erase m))
      (Finsupp.single (n.order + m.order) (monomial (t.erase n))) = _
  rw [R_single_swap fullData hT _ _
    ((-1 : ℂ) ^ ((t.erase n).card * (s.erase m).card))
    (hcomm (t.erase n) (s.erase m))]
  rw [Nat.add_comm n.order m.order]
  rfl

private theorem skew_sign (p q i j : ℕ) :
    (-1 : ℂ) ^ j * (-1 : ℂ) ^ (p + 1 + 1) * (-1 : ℂ) ^ i =
      -((-1 : ℂ) ^ ((p + 1) * (q + 1))) *
        ((-1 : ℂ) ^ i * (-1 : ℂ) ^ (q + 1 + 1) * (-1 : ℂ) ^ j) *
          (-1 : ℂ) ^ (q * p) := by
  rw [neg_one_pow_eq_pow_mod_two (p + 1 + 1),
    neg_one_pow_eq_pow_mod_two ((p + 1) * (q + 1)),
    neg_one_pow_eq_pow_mod_two (q + 1 + 1),
    neg_one_pow_eq_pow_mod_two (q * p)]
  have hp : p % 2 = 0 ∨ p % 2 = 1 := by omega
  have hq : q % 2 = 0 ∨ q % 2 = 1 := by omega
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    norm_num [Nat.add_mod, Nat.mul_mod, hp, hq] <;> ring

theorem monomialBracket_super_skew
    (hT : ∀ a b, fullTranslation (fullWedge a b) =
      fullWedge (fullTranslation a) b + fullWedge a (fullTranslation b))
    (hcomm : ∀ (s t : FullExteriorMonomial) (k : ℕ),
      fullWedge (monomial s) ((fullTranslation ^ k) (monomial t)) =
        (-1 : ℂ) ^ (s.card * t.card) •
          fullWedge ((fullTranslation ^ k) (monomial t)) (monomial s))
    (s t : FullExteriorMonomial) :
    monomialBracket s t =
      (-((-1 : ℂ) ^ (s.card * t.card))) •
        K fullData (monomialBracket t s) := by
  rw [monomialBracket_eq_sum, monomialBracket_eq_sum]
  simp only [map_sum, map_smul, Finset.smul_sum, K_wickTerm hT hcomm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hs : s.card = (s.erase m).card + 1 := by
    rw [Finset.card_erase_of_mem hm]
    have : 0 < s.card := Finset.card_pos.mpr ⟨m, hm⟩
    omega
  have ht : t.card = (t.erase n).card + 1 := by
    rw [Finset.card_erase_of_mem hn]
    have : 0 < t.card := Finset.card_pos.mpr ⟨n, hn⟩
    omega
  congr 1
  rw [kernelCoefficient_swap n m, Nat.add_comm n.order m.order]
  rw [hs, ht]
  have h := skew_sign (s.erase m).card (t.erase n).card (fullPosition m s) (fullPosition n t)
  linear_combination
    ((-1 : ℂ) ^ (m.order + n.order) * kernelCoefficient m n) * h

end KhanSL2.FullBC

