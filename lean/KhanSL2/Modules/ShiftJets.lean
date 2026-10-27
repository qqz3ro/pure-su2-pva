module

public import KhanSL2.Modules.ModeShifts
public import KhanSL2.Injectivity.SourceWordPairing
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

/-! Coefficient lowering on the actual translated representatives of the source generators. -/

noncomputable section
namespace KhanSL2.Modules

/-- A commutator identity for even derivations is determined on exterior generators. -/
theorem derivation_translation_commutator (D E : Module.End ℂ Cochain) (c : ℂ)
    (D1 : D 1 = 0) (E1 : E 1 = 0)
    (Dmul : ∀ u v, D (u*v) = D u * v + u * D v)
    (Emul : ∀ u v, E (u*v) = E u * v + u * E v)
    (hgen : ∀ v, D (translation (generator v)) =
      translation (D (generator v)) + c • E (generator v)) (u : Cochain) :
    D (translation u) = translation (D u) + c • E u := by
  induction u using cochain_induction with
  | hzero => simp
  | hone =>
    change D (translation 1) = translation (D 1) + c • E 1
    rw [show translation 1 = 0 from extendDerivation_one _, D1, E1]
    simp
  | hadd u v hu hv => simp only [map_add, hu, hv, smul_add]; module
  | hsmul a u hu => simp only [map_smul, hu, smul_add, smul_smul]; module
  | hgen v u hu =>
    change D (translation (generator v*u)) = translation (D (generator v*u)) + c • E (generator v*u)
    rw [translation_mul, map_add, Dmul, Dmul, Dmul, map_add, translation_mul, translation_mul,
      Emul, hgen, hu]
    simp only [smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module

theorem lowerB_zero_translation (u : Cochain) :
    lowerB 0 (translation u) = translation (lowerB 0 u) := by
  have h := derivation_translation_commutator (lowerB 0) (lowerB 0) 0
    (lowerB_one 0) (lowerB_one 0) (lowerB_mul 0) (lowerB_mul 0) (fun v => ?_) u
  · simpa using h
  · cases v <;> simp [translationGenerator, Mode.next, Mode.order, lowerBGenerator]

theorem lowerB_succ_translation (m : ℕ) (u : Cochain) :
    lowerB (m+1) (translation u) =
      translation (lowerB (m+1) u) + ((m+1 : ℕ) : ℂ) • lowerB m u := by
  apply derivation_translation_commutator _ _ _
    (lowerB_one _) (lowerB_one _) (lowerB_mul _) (lowerB_mul _) ?_ u
  intro v
  cases v with
  | c j a => simp [translationGenerator, Mode.next, Mode.order, lowerBGenerator]
  | b j a =>
    by_cases h : m+1 ≤ j
    · have hm : m ≤ j := by omega
      have hj : m+1 ≤ j+1 := by omega
      have hsub : j-(m+1)+1 = j-m := by omega
      have hsub' : j+1-(m+1) = j-m := by omega
      simp only [translation_generator, translationGenerator, Mode.next, map_smul,
        lowerB_generator, lowerBGenerator, if_pos h, if_pos hm, if_pos hj, hsub, hsub']
      rw [← add_smul]
      congr 1
      have hn : j-(m+1)+1+(m+1) = j+1 := by omega
      exact_mod_cast hn.symm
    · by_cases hm : m ≤ j
      · have he : j = m := by omega
        subst j
        simp [translationGenerator, Mode.next, Mode.order, lowerBGenerator]
      · have hj : ¬m+1 ≤ j+1 := by omega
        simp [translationGenerator, Mode.next, lowerBGenerator, h, hm, hj]

/-- The coefficient-count operator on the two actual canonical representatives. -/
theorem lowerB_zero_x : lowerB 0 xRepresentative = xRepresentative := by
  simp [xRepresentative, lowerB_mul, lowerBGenerator, ← cochain_mul_eq_wedge]

theorem lowerB_zero_y : lowerB 0 yRepresentative = (3 : ℂ) • yRepresentative := by
  simp only [yRepresentative, ← cochain_mul_eq_wedge, lowerB_mul, lowerB_generator,
    lowerBGenerator, Nat.zero_le, if_true, Nat.sub_zero, add_mul]
  module

theorem lowerB_succ_x (m : ℕ) : lowerB (m+1) xRepresentative = 0 := by
  simp [xRepresentative, lowerB_mul, lowerBGenerator, ← cochain_mul_eq_wedge]

theorem lowerB_succ_y (m : ℕ) : lowerB (m+1) yRepresentative = 0 := by
  simp [yRepresentative, lowerB_mul, lowerBGenerator, ← cochain_mul_eq_wedge]

/-- Falling-factorial Pascal identity, with no subtraction on complex scalars. -/
theorem descFactorial_pascal (n m : ℕ) :
    (n+1).descFactorial (m+1) = n.descFactorial (m+1) + (m+1)*n.descFactorial m := by
  rw [Nat.succ_descFactorial_succ]
  have h := Nat.descFactorial_mul_self n m
  nlinarith


/-- Lowering on translates of any vector killed by every positive lowering operator. -/
theorem lowerB_translation_pow (a : Cochain)
    (ha : ∀ m : ℕ, lowerB (m+1) a = 0) (n m : ℕ) :
    lowerB m ((translation ^ n) a) = (n.descFactorial m : ℂ) •
      (translation ^ (n-m)) (lowerB 0 a) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simp
    | succ m => simp [ha]
  | succ n ih =>
    cases m with
    | zero =>
      rw [pow_succ', Module.End.mul_apply, lowerB_zero_translation, ih]
      simp only [Nat.descFactorial_zero, Nat.cast_one, one_smul, Nat.sub_zero]
      rw [pow_succ', Module.End.mul_apply]
    | succ m =>
      rw [pow_succ' translation n, Module.End.mul_apply, lowerB_succ_translation,
        ih (m+1), ih m, map_smul, smul_smul]
      have ht : n+1-(m+1) = n-m := by omega
      rw [ht]
      by_cases h : m < n
      · have he : n-(m+1)+1 = n-m := by omega
        have hp : translation ((translation ^ (n-(m+1))) (lowerB 0 a)) =
            (translation ^ (n-m)) (lowerB 0 a) := by
          rw [← Module.End.mul_apply, ← pow_succ', he]
        rw [hp, ← add_smul]
        congr 1
        exact_mod_cast (descFactorial_pascal n m).symm
      · by_cases he : m = n
        · subst m
          rw [Nat.succ_descFactorial_succ]
          simp only [Nat.descFactorial_of_lt (by omega : n < n+1),
            Nat.cast_zero, zero_smul, map_zero, zero_add, Nat.sub_self,
            pow_zero, Module.End.one_apply, Nat.cast_mul]
        · have hn : n < m := by omega
          rw [Nat.descFactorial_of_lt (by omega : n+1 < m+1)]
          simp only [Nat.descFactorial_of_lt hn,
            Nat.descFactorial_of_lt (by omega : n < m+1),
            Nat.cast_zero, zero_smul, map_zero, mul_zero, add_zero]

/-- The even generator carries one coefficient factor. -/
theorem lowerB_xJet (m n : ℕ) :
    lowerB m ((translation ^ n) xRepresentative) =
      (n.descFactorial m : ℂ) • (translation ^ (n-m)) xRepresentative := by
  rw [lowerB_translation_pow xRepresentative lowerB_succ_x, lowerB_zero_x]

/-- The odd generator carries three coefficient factors. -/
theorem lowerB_yJet (m n : ℕ) :
    lowerB m ((translation ^ n) yRepresentative) =
      ((3 : ℂ) * (n.descFactorial m : ℂ)) • (translation ^ (n-m)) yRepresentative := by
  rw [lowerB_translation_pow yRepresentative lowerB_succ_y, lowerB_zero_y, map_smul,
    smul_smul, mul_comm]

end KhanSL2.Modules
