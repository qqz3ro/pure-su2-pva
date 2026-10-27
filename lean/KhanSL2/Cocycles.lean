module

public import KhanSL2.CE
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel

@[expose] public section

noncomputable section

namespace KhanSL2

@[simp]
theorem wedge_single (s t : ExteriorMonomial) (a b : ℂ) :
    wedge (Finsupp.single s a) (Finsupp.single t b) =
      (a * b) • monomialWedge s t := by
  simp [wedge, wedgeLinear, Finsupp.linearCombination_single, smul_smul]

@[simp]
theorem wedge_zero (u : Cochain) : wedge u 0 = 0 := by
  exact (wedgeLinear u).map_zero

@[simp]
theorem zero_wedge (u : Cochain) : wedge 0 u = 0 := by
  simp [wedge]

theorem q_single (s : ExteriorMonomial) (a : ℂ) :
    q (Finsupp.single s a) =
      a • ∑ m ∈ s, ((-1 : ℂ) ^ position m s) •
        wedge (qGenerator m) (Finsupp.single (s.erase m) 1) := by
  simp [q, extendDerivation, Finsupp.linearCombination_single]

theorem q_single_eq_zero (s : ExteriorMonomial) (a : ℂ)
    (h : ∀ m ∈ s, qGenerator m = 0) : q (Finsupp.single s a) = 0 := by
  rw [q_single]
  simp only [smul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro m hm
  simp [h m hm]

@[simp]
theorem q_one : q cochainOne = 0 := by
  simp [cochainOne, q_single]

@[simp]
theorem colorAction_one (a : Fin 3) : colorAction a cochainOne = 0 := by
  simp [colorAction, cochainOne, extendDerivation, Finsupp.linearCombination_single]

theorem one_mem_cycles : cochainOne ∈ relativeCycles := by
  constructor
  · simp [relativeInvariants]
  · exact q_one

theorem q_xRepresentative : q xRepresentative = 0 := by
  simp only [xRepresentative, map_neg, map_sum]
  suffices (∑ a : Fin 3, q (wedge (generator (.b 0 a))
      (generator (.c 0 a)))) = 0 by simp [this]
  apply Finset.sum_eq_zero
  intro a _
  simp only [generator, wedge_single, one_mul, one_smul]
  unfold monomialWedge
  split
  · apply q_single_eq_zero
    intro m hm
    simp only [Finset.mem_union, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> simp
  · simp

theorem q_yRepresentative : q yRepresentative = 0 := by
  simp [yRepresentative, generator, monomialWedge, inversionCount, q_single,
    position, Mode.code]

theorem colorAction_yRepresentative (a : Fin 3) :
    colorAction a yRepresentative = 0 := by
  fin_cases a <;>
    simp [colorAction, extendDerivation, colorGenerator, yRepresentative,
      wedge, wedgeLinear, generator, Finsupp.linearCombination_single,
      monomialWedge, inversionCount, position, epsilon, Mode.code,
      Mode.color, Mode.recolor, Fin.sum_univ_succ, ← Finset.insert_eq]

@[simp]
theorem bc_pair_order (j k : ℕ) (a b : Fin 3) :
    ({Mode.c j a, Mode.b k b} : Finset Mode) = {Mode.b k b, Mode.c j a} := by
  exact Finset.pair_comm _ _

set_option maxHeartbeats 2000000 in
theorem colorAction_xRepresentative (a : Fin 3) :
    colorAction a xRepresentative = 0 := by
  fin_cases a <;>
    simp [colorAction, extendDerivation, colorGenerator, xRepresentative,
      wedge, wedgeLinear, generator, Finsupp.linearCombination_single,
      monomialWedge, inversionCount, position, epsilon, Mode.code,
      Mode.color, Mode.recolor, Fin.sum_univ_succ, ← Finset.insert_eq,
      Finset.filter_insert, Finset.filter_singleton, Finset.erase_insert_of_ne]

theorem xRepresentative_mem_cycles : xRepresentative ∈ relativeCycles := by
  constructor
  · simp [relativeInvariants, colorAction_xRepresentative]
  · exact q_xRepresentative

theorem yRepresentative_mem_cycles : yRepresentative ∈ relativeCycles := by
  constructor
  · simp [relativeInvariants, colorAction_yRepresentative]
  · exact q_yRepresentative

def xClass : Cohomology :=
  classOf xRepresentative xRepresentative_mem_cycles

def yClass : Cohomology :=
  classOf yRepresentative yRepresentative_mem_cycles

end KhanSL2
