module

public import KhanSL2.Cocycles
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Elementary identities for the concrete Chevalley–Eilenberg operators

The exterior differential and the infinitesimal color actions are the exact
finite formulas in `CE`. The identities here identify their values on generators
and prove the structure-constant identities used in the differential calculation.
-/

noncomputable section

namespace KhanSL2

theorem Mode.code_injective : Function.Injective Mode.code := by
  intro m n h
  cases m with
  | b j a =>
    cases n with
    | b k b =>
      have hb := b.isLt
      simp only [Mode.code] at h
      have hj : j = k := by omega
      have hab : a = b := Fin.ext (by omega)
      subst hj
      subst hab
      rfl
    | c k b =>
      simp only [Mode.code] at h
      omega
  | c j a =>
    cases n with
    | b k b =>
      simp only [Mode.code] at h
      omega
    | c k b =>
      have hb := b.isLt
      simp only [Mode.code] at h
      have hj : j = k := by omega
      have hab : a = b := Fin.ext (by omega)
      subst hj
      subst hab
      rfl

@[simp] theorem inversionCount_empty_right (s : ExteriorMonomial) :
    inversionCount s ∅ = 0 := by
  simp [inversionCount]

@[simp] theorem inversionCount_empty_left (s : ExteriorMonomial) :
    inversionCount ∅ s = 0 := by
  simp [inversionCount]

@[simp] theorem monomialWedge_empty_right (s : ExteriorMonomial) :
    monomialWedge s ∅ = Finsupp.single s 1 := by
  simp [monomialWedge]

@[simp] theorem monomialWedge_empty_left (s : ExteriorMonomial) :
    monomialWedge ∅ s = Finsupp.single s 1 := by
  simp [monomialWedge]

@[simp] theorem wedge_one (u : Cochain) : wedge u cochainOne = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    change wedgeLinear (u + v) cochainOne = u + v
    simp only [map_add, LinearMap.add_apply]
    exact congrArg₂ (· + ·) hu hv
  | single s r =>
    simp [cochainOne]

@[simp] theorem one_wedge (u : Cochain) : wedge cochainOne u = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    change wedgeLinear cochainOne (u + v) = u + v
    rw [map_add]
    exact congrArg₂ (· + ·) hu hv
  | single s r =>
    simp [cochainOne]

@[simp] theorem extendDerivation_one (f : Mode → Cochain) :
    extendDerivation f cochainOne = 0 := by
  simp [extendDerivation, cochainOne, Finsupp.linearCombination_single]

@[simp] theorem extendDerivation_generator (f : Mode → Cochain) (m : Mode) :
    extendDerivation f (generator m) = f m := by
  simp only [extendDerivation, generator, Finsupp.linearCombination_single,
    one_smul, Finset.sum_singleton, Finset.erase_singleton]
  have hp : position m {m} = 0 := by
    have hf : Finset.filter (fun a => a.code < m.code) {m} = ∅ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty,
        iff_false, not_and]
      intro h
      subst a
      exact Nat.lt_irrefl _
    simp [position, hf]
  rw [hp, pow_zero, one_smul]
  exact wedge_one (f m)

@[simp] theorem q_generator (m : Mode) : q (generator m) = qGenerator m := by
  exact extendDerivation_generator qGenerator m

@[simp] theorem colorAction_generator (a : Fin 3) (m : Mode) :
    colorAction a (generator m) = colorGenerator a m := by
  exact extendDerivation_generator (colorGenerator a) m

@[simp] theorem translation_generator (m : Mode) :
    translation (generator m) = translationGenerator m := by
  exact extendDerivation_generator translationGenerator m

@[simp] theorem epsilon_self_left (a b : Fin 3) : epsilon a a b = 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [epsilon]

@[simp] theorem epsilon_self_right (a b : Fin 3) : epsilon a b b = 0 := by
  fin_cases a <;> fin_cases b <;> norm_num [epsilon]

theorem epsilon_rotate (a b c : Fin 3) : epsilon a b c = epsilon b c a := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [epsilon]

theorem epsilon_swap_left (a b c : Fin 3) : epsilon a b c = -epsilon b a c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [epsilon]

theorem epsilon_swap_right (a b c : Fin 3) : epsilon a b c = -epsilon a c b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> norm_num [epsilon]

/-- The Jacobi identity in the exact epsilon normalization used by `q`. -/
theorem epsilon_jacobi (a b c d : Fin 3) :
    (∑ e : Fin 3, epsilon a b e * epsilon e c d) +
      (∑ e : Fin 3, epsilon b c e * epsilon e a d) +
      (∑ e : Fin 3, epsilon c a e * epsilon e b d) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [epsilon, Fin.sum_univ_three]

/-- The invariant pairing is the Kronecker pairing in the color basis. -/
theorem epsilon_pairing_invariant (a b c : Fin 3) :
    epsilon a b c + epsilon a c b = 0 := by
  rw [epsilon_swap_right a b c]
  exact neg_add_cancel _

end KhanSL2
