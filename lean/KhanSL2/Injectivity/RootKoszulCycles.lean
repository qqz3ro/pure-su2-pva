module

public import KhanSL2.Injectivity.RootCycles
public import TauCeti.RingTheory.KoszulComplex.Basic

/-! # Closed exterior products of the explicit root cycles -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

variable {σ R : Type*} [Fintype σ] [CommRing R] [Algebra ℚ R]

/-- An exterior product of the explicit closed Cartan coefficient chains. -/
def rootKoszulWedge (u v : σ → R) {r : ℕ} (k : Fin r → ℕ) :
    ⋀[R]^r (ℕ →₀ R) :=
  exteriorPower.ιMulti R r (fun i => rootCycle u v (k i))

/-- The explicit wedges are genuine cycles for Tau Ceti's Koszul differential.
No exactness or regular-sequence hypothesis is needed. -/
theorem rootKoszulWedge_closed (u v : σ → R) {r : ℕ} (k : Fin (r + 1) → ℕ)
    (hk : ∀ i, Fintype.card σ < k i) :
    TauCeti.koszulDifferential (rootDifferential u v) r (rootKoszulWedge u v k) = 0 := by
  rw [rootKoszulWedge, TauCeti.koszulDifferential_ιMulti]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [rootCycle_closed u v (hk i), mul_zero, zero_smul]

end KhanSL2.Injectivity
