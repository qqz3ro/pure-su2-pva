module

public import KhanSL2.Injectivity.CartanRestriction
public import KhanSL2.Injectivity.FiniteSupport

/-! Cochains containing Cartan coordinates are orthogonal to root-only chains. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity.Cartan

def rootOnly : Submodule ℂ Cochain :=
  FiniteExterior.generatorsIn {m | ∀ i, m ≠ Mode.cartan i}

def hasCartan : Submodule ℂ Cochain :=
  FiniteExterior.supportedOn (fun s => ∃ i, Mode.cartan i ∈ s)

theorem rootOnly_one : (1 : Cochain) ∈ rootOnly :=
  FiniteExterior.one_mem_generatorsIn _

theorem rootOnly_mul {u v : Cochain} (hu : u ∈ rootOnly) (hv : v ∈ rootOnly) :
    u * v ∈ rootOnly := FiniteExterior.mul_mem_generatorsIn _ hu hv

@[simp] theorem rootOnly_neutral (j : ℕ) : generator (.neutral j) ∈ rootOnly := by
  exact FiniteExterior.generator_mem_generatorsIn _ _ (by simp)

@[simp] theorem rootOnly_plus (j : ℕ) : generator (.plus j) ∈ rootOnly := by
  exact FiniteExterior.generator_mem_generatorsIn _ _ (by simp)

@[simp] theorem rootOnly_minus (j : ℕ) : generator (.minus j) ∈ rootOnly := by
  exact FiniteExterior.generator_mem_generatorsIn _ _ (by simp)

theorem cartan_mem_hasCartan (j : ℕ) : generator (.cartan j) ∈ hasCartan :=
  FiniteExterior.monomial_mem_supportedOn _ _ ⟨j, Finset.mem_singleton_self _⟩

theorem hasCartan_mul {u : Cochain} (hu : u ∈ hasCartan) (v : Cochain) :
    u * v ∈ hasCartan := by
  refine FiniteExterior.supportedOn_mul (fun s => ∃i, Mode.cartan i ∈ s)
    (fun _ => True) (fun s => ∃i, Mode.cartan i ∈ s) ?_ hu ?_
  · intro s t hs _
    obtain ⟨i, hi⟩ := hs
    exact ⟨i, Finset.mem_union_left t hi⟩
  · intro s _hs
    trivial

theorem qGenerator_mem_hasCartan (m : Mode) : qGenerator m ∈ hasCartan := by
  cases m with
  | neutral j => exact hasCartan.zero_mem
  | cartan j => exact hasCartan.zero_mem
  | plus j =>
    apply hasCartan.neg_mem
    apply Submodule.sum_mem
    intro i _hi
    exact hasCartan_mul (cartan_mem_hasCartan i) _
  | minus j =>
    apply Submodule.sum_mem
    intro i _hi
    exact hasCartan_mul (cartan_mem_hasCartan i) _

theorem q_mem_hasCartan (u : Cochain) : q u ∈ hasCartan := by
  change FiniteExterior.extendDerivation Mode.code qGenerator u ∈ hasCartan
  rw [← FiniteExterior.finiteDerivation_eq Mode.code qGenerator
    (FiniteExterior.supportModes u) u (Finset.Subset.refl _),
    FiniteExterior.finiteDerivation_apply]
  apply Submodule.sum_mem
  intro m _hm
  exact hasCartan_mul (qGenerator_mem_hasCartan m) _

/-- Every chain without Cartan factors kills the full Cartan CE differential. -/
theorem rootOnly_pairing_q {c : Cochain} (hc : c ∈ rootOnly) (u : Cochain) :
    FiniteExterior.coefficientPairing c (q u) = 0 := by
  apply FiniteExterior.coefficientPairing_eq_zero_of_support
    (fun s => ∀a ∈ s, ∀i, a ≠ Mode.cartan i)
    (fun s => ∃i, Mode.cartan i ∈ s) _ hc (q_mem_hasCartan u)
  intro s hs ht
  obtain ⟨i, hi⟩ := ht
  exact hs (.cartan i) hi i rfl

end KhanSL2.Injectivity.Cartan
