module

public import KhanSL2.CETranslation
public import KhanSL2.Data

@[expose] public section

/-!
# The concrete relative Chevalley–Eilenberg complex

Every field of the original structural predicate is now a theorem about the
fixed finite formulas. No complex law is assumed in this construction.
-/

noncomputable section

namespace KhanSL2

/-- All foundational laws for the fixed restricted relative CE complex. -/
theorem relativeComplex_laws : RelativeComplexLaws where
  square_zero := q_square_zero
  invariant_preservation _ hu := invariant_q hu
  one_closed := q_one
  degree d u hu := by
    rcases d with ⟨k, b, s⟩
    simpa using q_degree hu
  odd_leibniz _ _ v hu := q_odd_leibniz hu v
  translation_commutes _ hu := q_translation_commutes hu

/-- The differential on invariant cochains, with its preservation proof supplied. -/
def relativeDifferential : Module.End ℂ relativeInvariants :=
  (q.domRestrict relativeInvariants).codRestrict relativeInvariants
    (fun u => invariant_q u.property)

@[simp] theorem relativeDifferential_coe (u : relativeInvariants) :
    (relativeDifferential u : Cochain) = q u := rfl

theorem relativeDifferential_square_zero (u : relativeInvariants) :
    relativeDifferential (relativeDifferential u) = 0 := by
  apply Subtype.ext
  exact q_square_zero u

/-- The image quotient in `CE` is the usual cycles modulo boundaries quotient. -/
theorem relative_boundaries_are_cycles :
    relativeInvariants.map q ≤ relativeCycles := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := hv
  exact ⟨invariant_q hu, q_square_zero u⟩

end KhanSL2
