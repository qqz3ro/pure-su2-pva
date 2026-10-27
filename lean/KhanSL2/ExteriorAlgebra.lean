module

public import KhanSL2.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Finite exterior multiplication, with its explicit ordered-monomial signs. -/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α]

abbrev Exterior (α : Type*) := Finset α →₀ ℂ

def inversionCount (code : α → ℕ) (s t : Finset α) : ℕ :=
  ∑ a ∈ s, (t.filter fun b => code b < code a).card

def monomialWedge (code : α → ℕ) (s t : Finset α) : Exterior α :=
  if Disjoint s t then
    Finsupp.single (s ∪ t) ((-1 : ℂ) ^ inversionCount code s t)
  else 0

def wedgeLinear (code : α → ℕ) : Exterior α →ₗ[ℂ] Exterior α →ₗ[ℂ] Exterior α :=
  Finsupp.linearCombination ℂ fun s =>
    Finsupp.linearCombination ℂ (monomialWedge code s)

def wedge (code : α → ℕ) (u v : Exterior α) : Exterior α := wedgeLinear code u v

def monomial (s : Finset α) : Exterior α := Finsupp.single s 1

def generator (a : α) : Exterior α := monomial {a}

@[simp] theorem wedge_zero_left (code : α → ℕ) (v : Exterior α) :
    wedge code 0 v = 0 := by simp [wedge]

@[simp] theorem wedge_zero_right (code : α → ℕ) (u : Exterior α) :
    wedge code u 0 = 0 := by simp [wedge]

theorem wedge_add_left (code : α → ℕ) (u v w : Exterior α) :
    wedge code (u + v) w = wedge code u w + wedge code v w := by simp [wedge]

theorem wedge_add_right (code : α → ℕ) (u v w : Exterior α) :
    wedge code u (v + w) = wedge code u v + wedge code u w := by simp [wedge]

theorem wedge_smul_left (code : α → ℕ) (r : ℂ) (u v : Exterior α) :
    wedge code (r • u) v = r • wedge code u v := by simp [wedge]

theorem wedge_smul_right (code : α → ℕ) (r : ℂ) (u v : Exterior α) :
    wedge code u (r • v) = r • wedge code u v := by simp [wedge]

@[simp] theorem wedge_single (code : α → ℕ) (s t : Finset α) (a b : ℂ) :
    wedge code (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • monomialWedge code s t := by
  simp [wedge, wedgeLinear, smul_smul]

@[simp] theorem wedge_monomial (code : α → ℕ) (s t : Finset α) :
    wedge code (monomial s) (monomial t) = monomialWedge code s t := by
  simp [monomial]

omit [DecidableEq α] in
@[simp] theorem inversionCount_empty_left (code : α → ℕ) (s : Finset α) :
    inversionCount code ∅ s = 0 := by simp [inversionCount]

omit [DecidableEq α] in
@[simp] theorem inversionCount_empty_right (code : α → ℕ) (s : Finset α) :
    inversionCount code s ∅ = 0 := by simp [inversionCount]

theorem inversionCount_union_left (code : α → ℕ) (s t u : Finset α)
    (hst : Disjoint s t) :
    inversionCount code (s ∪ t) u =
      inversionCount code s u + inversionCount code t u := by
  exact Finset.sum_union hst

theorem inversionCount_union_right (code : α → ℕ) (s t u : Finset α)
    (htu : Disjoint t u) :
    inversionCount code s (t ∪ u) =
      inversionCount code s t + inversionCount code s u := by
  simp only [inversionCount, Finset.filter_union]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.card_union_of_disjoint (htu.mono (Finset.filter_subset _ _)
    (Finset.filter_subset _ _))

@[simp] theorem monomialWedge_empty_left (code : α → ℕ) (s : Finset α) :
    monomialWedge code ∅ s = monomial s := by simp [monomialWedge, monomial]

@[simp] theorem monomialWedge_empty_right (code : α → ℕ) (s : Finset α) :
    monomialWedge code s ∅ = monomial s := by simp [monomialWedge, monomial]

theorem wedge_one_left (code : α → ℕ) (u : Exterior α) :
    wedge code (monomial ∅) u = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [wedge_add_right, hu, hv]
  | single s c => simp [monomial, monomialWedge]

theorem wedge_one_right (code : α → ℕ) (u : Exterior α) :
    wedge code u (monomial ∅) = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [wedge_add_left, hu, hv]
  | single s c => simp [monomial, monomialWedge]

theorem monomialWedge_assoc (code : α → ℕ) (s t u : Finset α) :
    wedge code (monomialWedge code s t) (monomial u) =
      wedge code (monomial s) (monomialWedge code t u) := by
  by_cases hst : Disjoint s t
  · by_cases hsu : Disjoint s u
    · by_cases htu : Disjoint t u
      · simp only [monomialWedge, hst, htu, Finset.disjoint_union_left,
          Finset.disjoint_union_right, hsu, and_self, ↓reduceIte, monomial,
          wedge_single, one_mul, mul_one]
        rw [inversionCount_union_left code s t u hst,
          inversionCount_union_right code s t u htu]
        simp only [Finsupp.smul_single, smul_eq_mul, ← pow_add, Finset.union_assoc]
        congr 2
        omega
      · simp [monomialWedge, hst, htu, Finset.disjoint_union_left, monomial]
    · by_cases htu : Disjoint t u <;>
        simp [monomialWedge, hst, hsu, htu, Finset.disjoint_union_left,
          Finset.disjoint_union_right, monomial]
  · by_cases htu : Disjoint t u <;>
      simp [monomialWedge, hst, htu, Finset.disjoint_union_right, monomial]

theorem wedge_assoc (code : α → ℕ) (u v w : Exterior α) :
    wedge code (wedge code u v) w = wedge code u (wedge code v w) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [wedge_add_left, hu, hv]
  | single s a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp [wedge_add_left, wedge_add_right, hu, hv]
    | single t b =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add u v hu hv => simp only [wedge_add_right, hu, hv]
      | single u c =>
        have hs : Finsupp.single s a = a • monomial s := by simp [monomial]
        have ht : Finsupp.single t b = b • monomial t := by simp [monomial]
        have hu : Finsupp.single u c = c • monomial u := by simp [monomial]
        rw [hs, ht, hu]
        simp only [wedge_smul_left, wedge_smul_right, wedge_monomial,
          smul_smul]
        rw [monomialWedge_assoc]
        simp [mul_assoc]

end KhanSL2.FiniteExterior

