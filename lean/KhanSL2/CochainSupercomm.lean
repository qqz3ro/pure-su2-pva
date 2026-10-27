module

public import KhanSL2.CEExterior
public import KhanSL2.ExteriorSupercomm
public import KhanSL2.CochainGrading
public import KhanSL2.PVA
public import Mathlib.Algebra.Ring.Commute

@[expose] public section

/-! The exact CE grading controls exterior supercommutativity and parity. -/

noncomputable section

namespace KhanSL2

theorem nat_parity_sign (n : ℕ) :
    (-1 : ℂ) ^ n = if (n : ℤ) % 2 = 0 then 1 else -1 := by
  rw [neg_one_pow_eq_pow_mod_two]
  change (-1 : ℂ) ^ (n % 2) = if (↑(n % 2) : ℤ) = 0 then 1 else -1
  by_cases h : n % 2 = 0
  · simp [h]
  · have h1 : n % 2 = 1 := by omega
    simp [h1]

theorem cochain_card_of_mem {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d)
    {s : ExteriorMonomial} (hs : s ∈ u.support) : (s.card : ℤ) = d.1 :=
  congrArg Prod.fst (hu hs)

theorem cochain_supercomm {d e : Degree} {u v : Cochain}
    (hu : u ∈ cochainPiece d) (hv : v ∈ cochainPiece e) :
    wedge u v = koszulSign d e • wedge v u := by
  by_cases hu0 : u = 0
  · subst u
    simp [wedge]
  by_cases hv0 : v = 0
  · subst v
    simp [wedge]
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hu0
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hv0
  have huc : ∀r ∈ u.support, r.card = s.card := by
    intro r hr
    exact_mod_cast (cochain_card_of_mem hu hr).trans (cochain_card_of_mem hu hs).symm
  have hvc : ∀r ∈ v.support, r.card = t.card := by
    intro r hr
    exact_mod_cast (cochain_card_of_mem hv hr).trans (cochain_card_of_mem hv ht).symm
  have hsign : (-1 : ℂ) ^ (s.card * t.card) = koszulSign d e := by
    rw [nat_parity_sign, Nat.cast_mul, cochain_card_of_mem hu hs,
      cochain_card_of_mem hv ht]
    rfl
  simpa only [← wedge_eq_generic, hsign] using
    FiniteExterior.wedge_supercomm_of_card Mode.code Mode.code_injective
      s.card t.card u v huc hvc

theorem cochainParity_of_mem {d : Degree} {u : Cochain} (hu : u ∈ cochainPiece d) :
    cochainParity u = koszulSign (1, 0, 0) d • u := by
  by_cases hu0 : u = 0
  · subst u
    simp
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hu0
  have huc : ∀r ∈ u.support, r.card = s.card := by
    intro r hr
    exact_mod_cast (cochain_card_of_mem hu hr).trans (cochain_card_of_mem hu hs).symm
  have hsign : (-1 : ℂ) ^ s.card = koszulSign (1, 0, 0) d := by
    rw [nat_parity_sign, cochain_card_of_mem hu hs]
    simp [koszulSign]
  simpa only [← cochainParity_apply, hsign] using FiniteExterior.parity_of_card s.card u huc

end KhanSL2
