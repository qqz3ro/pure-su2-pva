module

public import KhanSL2.Injectivity.SourceWordPairing
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp

/-! Factorial-normalized translations in the actual Cartan exterior algebra. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity.Cartan

theorem translation_pow_mul (n : ℕ) (a b : Cochain) :
    (translation ^ n) (a * b) =
      ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • ((translation ^ ij.1) a * (translation ^ ij.2) b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => (translation ^ i) a * (translation ^ j) b) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      translation_mul, nsmul_add, Finset.sum_add_distrib]
    rw [add_comm, add_left_cancel_iff]
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm]

def dividedTranslate (n : ℕ) (a : Cochain) : Cochain :=
  ((Nat.factorial n : ℂ)⁻¹) • (translation ^ n) a

theorem dividedTranslate_mul (n : ℕ) (a b : Cochain) :
    dividedTranslate n (a * b) =
      ∑ ij ∈ Finset.antidiagonal n, dividedTranslate ij.1 a * dividedTranslate ij.2 b := by
  rw [dividedTranslate, translation_pow_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  subst n
  simp only [dividedTranslate, smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have h : (((i + j).choose i : ℂ) * (Nat.factorial i : ℂ) *
      (Nat.factorial j : ℂ)) = (Nat.factorial (i + j) : ℂ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at hn
    exact_mod_cast hn
  have hi : (Nat.factorial i : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (Nat.factorial j : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : (Nat.factorial (i + j) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i + j)
  field_simp
  simpa only [mul_assoc] using h

theorem translation_pow_epsilon (color : ℕ → Mode)
    (hcolor : ∀ j, translation (generator (color j)) =
      ((j + 1 : ℕ) : ℂ) • generator (color (j + 1))) (n : ℕ) :
    (translation ^ n) (generator (color 0)) =
      (Nat.factorial n : ℂ) • generator (color n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, hn, map_smul, hcolor, smul_smul,
      Nat.factorial_succ, Nat.cast_mul, mul_comm]

theorem dividedTranslate_epsilon (color : ℕ → Mode)
    (hcolor : ∀ j, translation (generator (color j)) =
      ((j + 1 : ℕ) : ℂ) • generator (color (j + 1))) (n : ℕ) :
    dividedTranslate n (generator (color 0)) = generator (color n) := by
  rw [dividedTranslate, translation_pow_epsilon color hcolor, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_smul]

@[simp] theorem dividedTranslate_neutral (n : ℕ) :
    dividedTranslate n (generator (.neutral 0)) = generator (.neutral n) :=
  dividedTranslate_epsilon Mode.neutral (by intro j; simp [translationGenerator]) n

@[simp] theorem dividedTranslate_plus (n : ℕ) :
    dividedTranslate n (generator (.plus 0)) = generator (.plus n) :=
  dividedTranslate_epsilon Mode.plus (by intro j; simp [translationGenerator]) n

@[simp] theorem dividedTranslate_minus (n : ℕ) :
    dividedTranslate n (generator (.minus 0)) = generator (.minus n) :=
  dividedTranslate_epsilon Mode.minus (by intro j; simp [translationGenerator]) n

theorem translation_pow_cartan (n : ℕ) :
    (translation ^ n) (generator (.cartan 0)) =
      (Nat.factorial (n + 1) : ℂ) • generator (.cartan n) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, hn, map_smul, translation_generator,
      translationGenerator, smul_smul]
    congr 1
    simp only [Nat.factorial_succ, Nat.cast_mul]
    ring

@[simp] theorem dividedTranslate_cartan (n : ℕ) :
    dividedTranslate n (generator (.cartan 0)) = ((n + 1 : ℕ) : ℂ) • generator (.cartan n) := by
  rw [dividedTranslate, translation_pow_cartan, smul_smul, Nat.factorial_succ, Nat.cast_mul]
  have hn : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  congr 1
  field_simp

theorem dividedTranslate_xBase (n : ℕ) :
    dividedTranslate n xBase = ∑ ij ∈ Finset.antidiagonal n,
      ((ij.2 + 1 : ℕ) : ℂ) • (generator (.neutral ij.1) * generator (.cartan ij.2)) := by
  simp only [xBase, dividedTranslate_mul, dividedTranslate_neutral, dividedTranslate_cartan,
    mul_smul_comm]

theorem dividedTranslate_yBase (n : ℕ) :
    dividedTranslate n yBase = ∑ ij ∈ Finset.antidiagonal n,
      ∑ ab ∈ Finset.antidiagonal ij.1,
        (generator (.neutral ab.1) * generator (.plus ab.2)) * generator (.minus ij.2) := by
  simp only [yBase, dividedTranslate_mul, dividedTranslate_neutral, dividedTranslate_plus,
    dividedTranslate_minus, Finset.sum_mul]

def wordFactorial (ns : List ℕ) : ℂ := (ns.map fun n => (Nat.factorial n : ℂ)).prod

@[simp] theorem wordFactorial_nil : wordFactorial [] = 1 := rfl

@[simp] theorem wordFactorial_cons (n : ℕ) (ns : List ℕ) :
    wordFactorial (n :: ns) = (Nat.factorial n : ℂ) * wordFactorial ns := rfl

theorem wordFactorial_ne_zero (ns : List ℕ) : wordFactorial ns ≠ 0 := by
  induction ns with
  | nil => simp
  | cons n ns hn =>
    apply mul_ne_zero _ hn
    change (Nat.factorial n : ℂ) ≠ 0
    exact_mod_cast Nat.factorial_ne_zero n

def dividedJetProduct (u : Cochain) (ns : List ℕ) : Cochain :=
  (ns.map fun n => dividedTranslate n u).prod

@[simp] theorem dividedJetProduct_nil (u : Cochain) : dividedJetProduct u [] = 1 := rfl

@[simp] theorem dividedJetProduct_cons (u : Cochain) (n : ℕ) (ns : List ℕ) :
    dividedJetProduct u (n :: ns) = dividedTranslate n u * dividedJetProduct u ns := rfl

theorem translation_pow_eq_factorial_smul (n : ℕ) (u : Cochain) :
    (translation ^ n) u = (Nat.factorial n : ℂ) • dividedTranslate n u := by
  rw [dividedTranslate, smul_smul,
    mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero n), one_smul]

theorem jetProduct_eq_factorial_smul (u : Cochain) (ns : List ℕ) :
    jetProduct u ns = wordFactorial ns • dividedJetProduct u ns := by
  induction ns with
  | nil => simp
  | cons n ns hn =>
    rw [jetProduct_cons, hn, translation_pow_eq_factorial_smul,
      smul_mul_smul_comm, wordFactorial_cons, dividedJetProduct_cons]

def normalizedWord (xs ys : List ℕ) : Cochain :=
  dividedJetProduct xBase xs * dividedJetProduct yBase ys

theorem sourceWord_eq_factorial_smul (xs ys : List ℕ) :
    sourceWord xs ys = (wordFactorial xs * wordFactorial ys) • normalizedWord xs ys := by
  rw [sourceWord, jetProduct_eq_factorial_smul, jetProduct_eq_factorial_smul,
    smul_mul_smul_comm]
  rfl

theorem normalizedWord_pairing (f : Cochain →ₗ[ℂ] ℂ) (xs ys : List ℕ) :
    f (sourceWord xs ys) / (wordFactorial xs * wordFactorial ys) = f (normalizedWord xs ys) := by
  rw [sourceWord_eq_factorial_smul, map_smul, smul_eq_mul]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (wordFactorial_ne_zero xs) (wordFactorial_ne_zero ys))

end KhanSL2.Injectivity.Cartan
