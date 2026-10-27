module

public import KhanSL2.BCBracketDegree
public import KhanSL2.CELeibniz

@[expose] public section

/-! Full skew symmetry and the right super-Leibniz identity of the concrete bracket. -/

noncomputable section

namespace KhanSL2.BC

open LambdaPolynomial PolynomialCalculus

theorem bracket_super_skew (d e : Degree) (a b : Cochain)
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e) :
    bracket a b = (-koszulSign d e) •
      minusVariableMinusTranslation translation (bracket b a) := by
  rw [show minusVariableMinusTranslation translation (bracket b a) =
      K cochainData (bracket b a) from (K_apply cochainData (bracket b a)).symm]
  rw [← a.sum_single, ← b.sum_single]
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply, bracket_single, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  rw [monomialBracket_super_skew translation_wedge translated_monomial_supercomm]
  have hsign : (-1 : ℂ) ^ (s.card * t.card) = koszulSign d e := by
    rw [nat_parity_sign, Nat.cast_mul, cochain_card_of_mem ha hs,
      cochain_card_of_mem hb ht]
    rfl
  rw [hsign, smul_smul]
  congr 1
  ring

@[simp] theorem mulRight_cochainOne (p : LambdaPolynomial Cochain) :
    mulRight cochainData p cochainOne = p := by
  apply Finsupp.ext
  intro j
  rw [mulRight_apply]
  change wedge (p j) cochainOne = p j
  exact wedge_cochainOne (p j)

@[simp] theorem bracket_monomial_generator (s : ExteriorMonomial) (m : Mode) :
    bracket (monomial s) (generator m) = monomialGeneratorAction s m := by
  have h : ({m} : Finset Mode).filter (fun a => a.code < m.code) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl m.code
  simp only [monomial, generator, bracket_single, one_mul, one_smul,
    monomialBracket, Finset.sum_singleton, position, h, Finset.card_empty,
    pow_zero, one_smul, Finset.erase_singleton]
  exact mulRight_cochainOne _

theorem bracket_generator_left (m : Mode) (b : Cochain) :
    bracket (generator m) b = generatorAction m b := by
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc => simp [hb, hc]
  | single s r =>
    simp only [generator, bracket_single, one_mul, generatorAction_single]
    congr 1
    have hmul (q : ℂ) (v : Cochain) :
        cochainData.mul (q • cochainOne) v = q • v := by
      change (q • (1 : Cochain)) * v = q • v
      simp
    simp only [monomialBracket, monomialGeneratorAction_singleton,
      kernel, mulRight_single, hmul, generatorActionMonomial]

/-- Each coefficient of the bracket is the exterior derivation determined
by its values on the odd mode generators. -/
theorem bracket_coefficient_eq_extendDerivation (a b : Cochain) (j : ℕ) :
    bracket a b j =
      extendDerivation (fun m => bracket a (generator m) j) b := by
  induction a using Finsupp.induction_linear with
  | zero => simp [extendDerivation, Finsupp.linearCombination_apply, wedge]
  | add a c ha hc =>
    rw [show bracket (a + c) b j = bracket a b j + bracket c b j by simp]
    rw [ha, hc]
    simp only [extendDerivation, Finsupp.linearCombination_apply, Finsupp.sum,
      map_add, LinearMap.add_apply, Finsupp.add_apply,
      wedge, smul_add, Finset.sum_add_distrib]
  | single s r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b c hb hc => simp [hb, hc]
    | single t u =>
      have hg (m : Mode) :
          bracket (Finsupp.single s r) (generator m) =
            r • monomialGeneratorAction s m := by
        have hsr : Finsupp.single s r = r • monomial s := by simp [monomial]
        rw [hsr]
        simp only [map_smul, LinearMap.smul_apply, bracket_monomial_generator]
      simp only [bracket_single, Finsupp.smul_apply, monomialBracket,
        Finset.sum_apply', mulRight_apply, cochainData,
        extendDerivation, Finsupp.linearCombination_single, hg]
      simp only [wedge, map_smul, LinearMap.smul_apply, smul_smul,
        Finset.smul_sum, monomial]
      apply Finset.sum_congr rfl
      intro m _
      congr 1
      ring

theorem bracket_super_leibniz (d e : Degree) (a b c : Cochain)
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e) :
    bracket a (wedge b c) =
      mulRight cochainData (bracket a b) c +
        koszulSign d e • mulLeft cochainData b (bracket a c) := by
  apply Finsupp.ext
  intro j
  simp only [Finsupp.add_apply, Finsupp.smul_apply, mulRight_apply, mulLeft_apply,
    cochainData]
  rw [bracket_coefficient_eq_extendDerivation a (wedge b c) j,
    bracket_coefficient_eq_extendDerivation a b j,
    bracket_coefficient_eq_extendDerivation a c j]
  apply FiniteExterior.extendDerivation_wedge Mode.code Mode.code_injective
  intro m
  change wedge (bracket a (generator m) j) (cochainParity b) =
    koszulSign d e • wedge b (bracket a (generator m) j)
  rw [cochainParity_of_mem hb]
  have hm := bracket_degree d _ a (generator m) j ha (cochain_generator_mem m)
  rw [show ∀ (r : ℂ) (u v : Cochain), wedge u (r • v) = r • wedge u v from
    fun r u v => by simp [wedge]]
  rw [cochain_supercomm hm hb, smul_smul]
  have hsign : koszulSign (1, 0, 0) e *
      koszulSign (d.bracket (1, (m.bCount : ℤ), (m.weight : ℤ)) j) e =
        koszulSign d e := by
    have hd : d.1 % 2 = 0 ∨ d.1 % 2 = 1 := by omega
    have he : e.1 % 2 = 0 ∨ e.1 % 2 = 1 := by omega
    rcases hd with hd | hd <;> rcases he with he | he <;>
      norm_num [koszulSign, Degree.bracket, Int.mul_emod, Int.sub_emod,
        Int.add_emod, hd, he]
  rw [hsign]

end KhanSL2.BC
