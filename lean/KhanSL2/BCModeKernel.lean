module

public import KhanSL2.Data
public import KhanSL2.LambdaPolynomialLemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The normalized constant `bc` kernels

All jet generators are odd. The coefficient convention here is the ordinary
coefficient of a power of lambda, with the factorials supplied explicitly by
the divided-power jet normalization.
-/

noncomputable section

namespace KhanSL2

namespace Mode

/-- Jet order, remembering that `c j a` denotes `c_(j+1)^a`. -/
def order : Mode → ℕ
  | .b j _ => j
  | .c j _ => j + 1

def pairsWith : Mode → Mode → Prop
  | .b _ a, .c _ d => a = d
  | .c _ a, .b _ d => a = d
  | _, _ => False

instance (m n : Mode) : Decidable (pairsWith m n) := by
  cases m <;> cases n <;> unfold pairsWith <;> infer_instance

theorem pairsWith_comm (m n : Mode) : pairsWith m n ↔ pairsWith n m := by
  cases m <;> cases n <;> simp [pairsWith, eq_comm]

@[simp] theorem order_next (m : Mode) : m.next.order = m.order + 1 := by
  cases m <;> rfl

@[simp] theorem translationCoefficient_order (m : Mode) :
    m.translationCoefficient = m.order + 1 := by
  cases m <;> rfl

@[simp] theorem next_pairsWith (m n : Mode) :
    m.next.pairsWith n ↔ m.pairsWith n := by
  cases m <;> cases n <;> rfl

@[simp] theorem pairsWith_next (m n : Mode) :
    m.pairsWith n.next ↔ m.pairsWith n := by
  cases m <;> cases n <;> rfl

theorem pairsWith_bCount (m n : Mode) (h : m.pairsWith n) :
    m.bCount + n.bCount = 1 := by
  cases m <;> cases n <;> simp_all [pairsWith, bCount]

theorem pairsWith_weight (m n : Mode) (h : m.pairsWith n) :
    m.weight + n.weight = m.order + n.order + 1 := by
  cases m <;> cases n <;> simp_all [pairsWith, weight, order] <;> omega

end Mode

namespace BC

def kernelCoefficient (m n : Mode) : ℂ :=
  if m.pairsWith n then
    (-1 : ℂ) ^ m.order /
      ((Nat.factorial m.order : ℂ) * (Nat.factorial n.order : ℂ))
  else 0

def kernel (m n : Mode) : LambdaPolynomial Cochain :=
  Finsupp.single (m.order + n.order) (kernelCoefficient m n • cochainOne)

theorem pairsWith_of_kernelCoefficient_ne_zero (m n : Mode)
    (h : kernelCoefficient m n ≠ 0) : m.pairsWith n := by
  by_contra hp
  simp [kernelCoefficient, hp] at h

@[simp] theorem kernel_bb (j k : ℕ) (a b : Fin 3) :
    kernel (.b j a) (.b k b) = 0 := by
  simp [kernel, kernelCoefficient, Mode.pairsWith]

@[simp] theorem kernel_cc (j k : ℕ) (a b : Fin 3) :
    kernel (.c j a) (.c k b) = 0 := by
  simp [kernel, kernelCoefficient, Mode.pairsWith]

theorem kernel_bc (j k : ℕ) (a b : Fin 3) :
    kernel (.b j a) (.c k b) =
      Finsupp.single (j + k + 1)
        ((if a = b then
          (-1 : ℂ) ^ j /
            ((Nat.factorial j : ℂ) * (Nat.factorial (k + 1) : ℂ))
          else 0) • cochainOne) := by
  simp [kernel, kernelCoefficient, Mode.order, Mode.pairsWith, Nat.add_assoc]

theorem kernel_cb (j k : ℕ) (a b : Fin 3) :
    kernel (.c j a) (.b k b) =
      Finsupp.single (j + k + 1)
        ((if a = b then
          (-1 : ℂ) ^ (j + 1) /
            ((Nat.factorial (j + 1) : ℂ) * (Nat.factorial k : ℂ))
          else 0) • cochainOne) := by
  simp [kernel, kernelCoefficient, Mode.order, Mode.pairsWith,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem factorial_ne_zero (j : ℕ) : (Nat.factorial j : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero j

theorem kernelCoefficient_next_left (m n : Mode) :
    (m.translationCoefficient : ℂ) * kernelCoefficient m.next n =
      -kernelCoefficient m n := by
  simp only [kernelCoefficient, Mode.next_pairsWith, Mode.order_next,
    Mode.translationCoefficient_order]
  split_ifs with h
  · simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hm := factorial_ne_zero m.order
    have hn := factorial_ne_zero n.order
    have hi : (m.order : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m.order
    push_cast
    field_simp [hm, hn, hi]
  · simp

theorem kernelCoefficient_next_right (m n : Mode) :
    (n.translationCoefficient : ℂ) * kernelCoefficient m n.next =
      kernelCoefficient m n := by
  simp only [kernelCoefficient, Mode.pairsWith_next, Mode.order_next,
    Mode.translationCoefficient_order]
  split_ifs with h
  · simp only [Nat.factorial_succ, Nat.cast_mul]
    have hm := factorial_ne_zero m.order
    have hn := factorial_ne_zero n.order
    have hi : (n.order : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n.order
    push_cast
    field_simp [hm, hn, hi]
  · simp

theorem kernel_next_left (m n : Mode) :
    (m.translationCoefficient : ℂ) • kernel m.next n =
      -(kernel m n).shift := by
  simp only [kernel, Mode.order_next, Finsupp.smul_single,
    LambdaPolynomial.shift_single, ← Finsupp.single_neg, smul_smul, neg_smul]
  rw [kernelCoefficient_next_left]
  simp [neg_smul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem kernel_next_right (m n : Mode) :
    (n.translationCoefficient : ℂ) • kernel m n.next =
      (kernel m n).shift := by
  simp only [kernel, Mode.order_next, Finsupp.smul_single,
    LambdaPolynomial.shift_single, smul_smul]
  rw [kernelCoefficient_next_right]
  congr 1

theorem kernelCoefficient_swap (m n : Mode) :
    kernelCoefficient m n =
      (-1 : ℂ) ^ (m.order + n.order) * kernelCoefficient n m := by
  by_cases h : m.pairsWith n
  · have h' : n.pairsWith m := (Mode.pairsWith_comm m n).mp h
    simp only [kernelCoefficient, ite_eq_left h, ite_eq_left h']
    rw [← mul_div_assoc, pow_add, mul_assoc, ← mul_pow]
    simp [mul_comm]
  · have h' : ¬ n.pairsWith m := by
      simpa only [Mode.pairsWith_comm n m] using h
    simp [kernelCoefficient, h, h']

end BC
end KhanSL2
