module

public import KhanSL2.CE

/-!
# Finite chains and functionals on the actual cohomology quotient

The coefficient pairing is bilinear, with no complex conjugation. A finite
chain whose pairing vanishes on `q` defines a functional on the existing
relative cohomology. The vanishing condition is imposed on all cochains,
which is stronger than vanishing on the invariant boundaries defining the
quotient. No invariant-chain or coinvariant identification is needed.
-/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

/-- Finite polynomial-mode chains in the basis dual to `Cochain`. -/
abbrev Chain := ExteriorMonomial →₀ ℂ

/-- The finite coefficient pairing, linear in both arguments. -/
def chainPairing : Chain →ₗ[ℂ] Cochain →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun s => Finsupp.lapply s

@[simp] theorem chainPairing_single (s : ExteriorMonomial) (z : ℂ) (u : Cochain) :
    chainPairing (Finsupp.single s z) u = z * u s := by
  simp [chainPairing]

@[simp] theorem chainPairing_zero (u : Cochain) : chainPairing 0 u = 0 := by
  simp

/-- The condition needed to descend a functional through the actual quotient. -/
def AnnihilatesDifferential (f : Cochain →ₗ[ℂ] ℂ) : Prop :=
  ∀ u : Cochain, f (q u) = 0

theorem annihilatesDifferential_iff_monomials (f : Cochain →ₗ[ℂ] ℂ) :
    AnnihilatesDifferential f ↔
      ∀ s : ExteriorMonomial, f (q (Finsupp.single s 1)) = 0 := by
  constructor
  · exact fun h s => h (Finsupp.single s 1)
  · intro h u
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv, add_zero]
    | single s z =>
      have hz : Finsupp.single s z = z • (Finsupp.single s 1 : Cochain) := by
        simp
      rw [hz, map_smul, map_smul, h, smul_zero]

/-- A functional vanishing on all CE coboundaries descends to the relative
cohomology already used by the canonical map. -/
def descendFunctional (f : Cochain →ₗ[ℂ] ℂ) (hf : AnnihilatesDifferential f) :
    Cohomology →ₗ[ℂ] ℂ :=
  relativeBoundaries.liftQ (f.comp relativeCycles.subtype) (by
    intro u hu
    change (u : Cochain) ∈ relativeInvariants.map q at hu
    obtain ⟨v, _, hv⟩ := hu
    change f (u : Cochain) = 0
    rw [← hv]
    exact hf v)

@[simp] theorem descendFunctional_classOf
    (f : Cochain →ₗ[ℂ] ℂ) (hf : AnnihilatesDifferential f)
    (u : Cochain) (hu : u ∈ relativeCycles) :
    descendFunctional f hf (classOf u hu) = f u := rfl

/-- A finite cycle gives a well-defined cohomology functional. -/
def cycleFunctional (c : Chain) (hc : AnnihilatesDifferential (chainPairing c)) :
    Cohomology →ₗ[ℂ] ℂ :=
  descendFunctional (chainPairing c) hc

@[simp] theorem cycleFunctional_classOf
    (c : Chain) (hc : AnnihilatesDifferential (chainPairing c))
    (u : Cochain) (hu : u ∈ relativeCycles) :
    cycleFunctional c hc (classOf u hu) = chainPairing c u := rfl

theorem pairing_eq_zero_of_classOf_eq_zero
    (f : Cochain →ₗ[ℂ] ℂ) (hf : AnnihilatesDifferential f)
    (u : Cochain) (hu : u ∈ relativeCycles) (hz : classOf u hu = 0) :
    f u = 0 := by
  rw [← descendFunctional_classOf f hf u hu, hz, map_zero]

/-- Restriction to any explicitly defined cochain model is sufficient; only
commutation with the concrete differential is required. -/
theorem annihilatesDifferential_comp
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (restriction : Cochain →ₗ[ℂ] V) (d : V →ₗ[ℂ] V)
    (hrestriction : ∀ u, restriction (q u) = d (restriction u))
    (f : V →ₗ[ℂ] ℂ) (hf : ∀ v, f (d v) = 0) :
    AnnihilatesDifferential (f.comp restriction) := by
  intro u
  change f (restriction (q u)) = 0
  rw [hrestriction]
  exact hf (restriction u)

end KhanSL2.Injectivity
