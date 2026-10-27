module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Minimal energy of a weight in the exterior algebra of positive sl₂ currents.
Mode index `n` denotes physical current degree `n+1`. A basis wedge is described
by its three finite sets of positive-, zero-, and negative-root mode indices. -/

open scoped BigOperators

namespace KhanSL2.BGG

/-- The least energy of `n` distinct positive modes. -/
def triangular (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, (i + 1)

@[simp] theorem triangular_zero : triangular 0 = 0 := rfl

@[simp] theorem triangular_succ (n : ℕ) :
    triangular (n + 1) = triangular n + (n + 1) := by
  simp [triangular, Finset.sum_range_succ]

theorem two_mul_triangular (n : ℕ) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [triangular_succ, mul_add, ih]; ring

theorem triangular_strictMono : StrictMono triangular := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [triangular_succ]
  omega

/-- The sum of physical mode degrees for one root color. -/
def modeEnergy (s : Finset ℕ) : ℕ := ∑ n ∈ s, (n + 1)

@[simp] theorem modeEnergy_empty : modeEnergy ∅ = 0 := rfl

@[simp] theorem modeEnergy_range (n : ℕ) : modeEnergy (Finset.range n) = triangular n := rfl

theorem modeEnergy_insert {a : ℕ} {s : Finset ℕ} (ha : a ∉ s) :
    modeEnergy (insert a s) = (a + 1) + modeEnergy s := by
  exact Finset.sum_insert ha

theorem triangular_card_le_modeEnergy (s : Finset ℕ) :
    triangular s.card ≤ modeEnergy s := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := fun h => (Nat.lt_irrefl a) (hmax a h)
    have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (hmax x hx)
    have hc : s.card ≤ a := by simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ha, triangular_succ, modeEnergy_insert ha]
    omega

theorem modeEnergy_eq_triangular_card_iff (s : Finset ℕ) :
    modeEnergy s = triangular s.card ↔ s = Finset.range s.card := by
  constructor
  · induction s using Finset.induction_on_max with
    | empty => simp
    | insert a s hmax ih =>
      intro h
      have ha : a ∉ s := fun h => (Nat.lt_irrefl a) (hmax a h)
      have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.mpr (hmax x hx)
      have hc : s.card ≤ a := by simpa using Finset.card_le_card hsub
      have hs := triangular_card_le_modeEnergy s
      rw [Finset.card_insert_of_notMem ha, triangular_succ, modeEnergy_insert ha] at h
      have has : a = s.card := by omega
      have hes : modeEnergy s = triangular s.card := by omega
      have hsr := ih hes
      rw [Finset.card_insert_of_notMem ha, has, hsr]
      ext k
      simp only [Finset.mem_insert, Finset.mem_range, Finset.card_range]
      omega
  · intro h
    conv_lhs => rw [h]
    rfl

theorem modeEnergy_eq_zero_iff (s : Finset ℕ) : modeEnergy s = 0 ↔ s = ∅ := by
  constructor
  · intro h
    apply Finset.ext
    intro a
    simp only [Finset.notMem_empty, iff_false]
    intro ha
    have hle : a + 1 ≤ modeEnergy s :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
    omega
  · rintro rfl
    rfl

/-- An exterior basis support, with independent finite sets for the three colors. -/
@[ext] structure RootSupport where
  pos : Finset ℕ
  neutral : Finset ℕ
  neg : Finset ℕ
  deriving DecidableEq

namespace RootSupport

def degree (w : RootSupport) : ℕ := w.pos.card + w.neutral.card + w.neg.card

/-- Half the eigenvalue of the Cartan generator. -/
def weight (w : RootSupport) : ℤ := (w.pos.card : ℤ) - (w.neg.card : ℤ)

def energy (w : RootSupport) : ℕ :=
  modeEnergy w.pos + modeEnergy w.neutral + modeEnergy w.neg

/-- The support of `e₁ ∧ e₂ ∧ ... ∧ eⱼ`. -/
def highest (j : ℕ) : RootSupport := ⟨Finset.range j, ∅, ∅⟩

@[simp] theorem highest_degree (j : ℕ) : (highest j).degree = j := by
  simp [highest, degree]

@[simp] theorem highest_weight (j : ℕ) : (highest j).weight = j := by
  simp [highest, weight]

@[simp] theorem highest_energy (j : ℕ) : (highest j).energy = triangular j := by
  simp [highest, energy]

/-- A nonnegative weight has triangular minimum energy. -/
theorem triangular_le_energy (w : RootSupport) (j : ℕ) (hw : w.weight = j) :
    triangular j ≤ w.energy := by
  have hj : j ≤ w.pos.card := by dsimp [weight] at hw; omega
  have hm := triangular_strictMono.monotone hj
  have hp := triangular_card_le_modeEnergy w.pos
  dsimp [energy]
  omega

/-- Equality in the energy bound singles out one exterior basis word. -/
theorem eq_highest_of_minimal_energy (w : RootSupport) (j : ℕ)
    (hw : w.weight = j) (he : w.energy = triangular j) : w = highest j := by
  have hj : j ≤ w.pos.card := by dsimp [weight] at hw; omega
  have hm := triangular_strictMono.monotone hj
  have hp := triangular_card_le_modeEnergy w.pos
  have hc : w.pos.card = j := by
    apply triangular_strictMono.injective
    dsimp [energy] at he
    omega
  have hpos : modeEnergy w.pos = triangular w.pos.card := by
    dsimp [energy] at he
    rw [hc] at hp ⊢
    omega
  have hn : modeEnergy w.neutral = 0 := by
    dsimp [energy] at he
    rw [hc] at hp
    omega
  have hf : modeEnergy w.neg = 0 := by
    dsimp [energy] at he
    rw [hc] at hp
    omega
  apply RootSupport.ext
  · change w.pos = Finset.range j
    rw [← hc]
    exact (modeEnergy_eq_triangular_card_iff w.pos).mp hpos
  · exact (modeEnergy_eq_zero_iff w.neutral).mp hn
  · exact (modeEnergy_eq_zero_iff w.neg).mp hf

theorem degree_eq_of_minimal_energy (w : RootSupport) (j : ℕ)
    (hw : w.weight = j) (he : w.energy = triangular j) : w.degree = j := by
  rw [eq_highest_of_minimal_energy w j hw he, highest_degree]

end RootSupport
end KhanSL2.BGG