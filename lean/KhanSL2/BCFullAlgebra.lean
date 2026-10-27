module

public import KhanSL2.BCFullGrading
public import KhanSL2.CochainSupercomm

@[expose] public section

/-! The full exterior algebra, with its even jet translation. -/

noncomputable section

namespace KhanSL2

theorem fullWedge_assoc (u v w : FullCochain) :
    fullWedge (fullWedge u v) w = fullWedge u (fullWedge v w) :=
  FiniteExterior.wedge_assoc FullMode.code u v w

@[simp] theorem fullOne_wedge (u : FullCochain) : fullWedge fullOne u = u :=
  FiniteExterior.wedge_one_left FullMode.code u

@[simp] theorem fullWedge_one (u : FullCochain) : fullWedge u fullOne = u :=
  FiniteExterior.wedge_one_right FullMode.code u

@[simp] theorem fullWedge_zero (u : FullCochain) : fullWedge u 0 = 0 :=
  (fullWedgeLinear u).map_zero

@[simp] theorem fullZero_wedge (u : FullCochain) : fullWedge 0 u = 0 :=
  fullWedgeLinear.map_zero₂ u

@[simp] theorem fullWedge_single (s t : FullExteriorMonomial) (r u : ℂ) :
    fullWedge (Finsupp.single s r) (Finsupp.single t u) =
      (r * u) • fullMonomialWedge s t := by
  simp [fullWedge, FiniteExterior.wedge, FiniteExterior.wedgeLinear,
    fullMonomialWedge, smul_smul]

theorem full_card_of_mem {d : Degree} {u : FullCochain} (hu : u ∈ fullPiece d)
    {s : FullExteriorMonomial} (hs : s ∈ u.support) : (s.card : ℤ) = d.1 :=
  congrArg Prod.fst (hu hs)

theorem full_supercomm {d e : Degree} {u v : FullCochain}
    (hu : u ∈ fullPiece d) (hv : v ∈ fullPiece e) :
    fullWedge u v = koszulSign d e • fullWedge v u := by
  by_cases hu0 : u = 0
  · subst u
    simp
  by_cases hv0 : v = 0
  · subst v
    simp
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hu0
  obtain ⟨t, ht⟩ := Finsupp.support_nonempty_iff.mpr hv0
  have huc : ∀r ∈ u.support, r.card = s.card := by
    intro r hr
    exact_mod_cast (full_card_of_mem hu hr).trans (full_card_of_mem hu hs).symm
  have hvc : ∀r ∈ v.support, r.card = t.card := by
    intro r hr
    exact_mod_cast (full_card_of_mem hv hr).trans (full_card_of_mem hv ht).symm
  have hsign : (-1 : ℂ) ^ (s.card * t.card) = koszulSign d e := by
    rw [nat_parity_sign, Nat.cast_mul, full_card_of_mem hu hs, full_card_of_mem hv ht]
    rfl
  simpa only [fullWedge, hsign] using
    FiniteExterior.wedge_supercomm_of_card FullMode.code FullMode.code_injective
      s.card t.card u v huc hvc

theorem fullParity_of_mem {d : Degree} {u : FullCochain} (hu : u ∈ fullPiece d) :
    fullParity u = koszulSign (1, 0, 0) d • u := by
  by_cases hu0 : u = 0
  · subst u
    simp
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hu0
  have huc : ∀r ∈ u.support, r.card = s.card := by
    intro r hr
    exact_mod_cast (full_card_of_mem hu hr).trans (full_card_of_mem hu hs).symm
  have hsign : (-1 : ℂ) ^ s.card = koszulSign (1, 0, 0) d := by
    rw [nat_parity_sign, full_card_of_mem hu hs]
    simp [koszulSign]
  change FiniteExterior.parityLinear u = _
  simpa only [hsign] using FiniteExterior.parity_of_card s.card u huc

@[simp] theorem fullParity_generator (m : FullMode) :
    fullParity (fullGenerator m) = -fullGenerator m :=
  FiniteExterior.parity_generator m

@[simp] theorem fullParity_involutive (u : FullCochain) :
    fullParity (fullParity u) = u := FiniteExterior.parity_involutive u

@[simp] theorem fullTranslation_one : fullTranslation fullOne = 0 :=
  by simp [fullTranslation, fullOne, FiniteExterior.extendDerivation_monomial]

@[simp] theorem fullTranslation_generator (m : FullMode) :
    fullTranslation (fullGenerator m) = fullTranslationGenerator m := by
  have h : ({m} : Finset FullMode).filter
      (fun a => FullMode.code a < FullMode.code m) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl (FullMode.code m)
  simp only [fullGenerator, FiniteExterior.generator,
    fullTranslation, FiniteExterior.extendDerivation_monomial,
    Finset.sum_singleton, FiniteExterior.position, h, Finset.card_empty,
    pow_zero, one_smul, Finset.erase_singleton]
  exact FiniteExterior.wedge_one_right FullMode.code _

@[simp] theorem fullTranslation_ghost (a : Fin 3) :
    fullTranslation (ghost a) = fullGenerator (.inr (.c 0 a)) := by
  simp [ghost, fullTranslationGenerator, FullMode.translationCoefficient,
    FullMode.order, FullMode.next]

theorem fullTranslationGenerator_parity (m : FullMode) :
    fullParity (fullTranslationGenerator m) = -fullTranslationGenerator m := by
  simp [fullTranslationGenerator, smul_neg]

theorem fullTranslation_wedge (u v : FullCochain) :
    fullTranslation (fullWedge u v) =
      fullWedge (fullTranslation u) v + fullWedge u (fullTranslation v) := by
  apply FiniteExterior.extendDerivation_wedge_twist FullMode.code FullMode.code_injective
    fullTranslationGenerator u v u
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd FullMode.code FullMode.code_injective
    (fullTranslationGenerator m) (fullTranslationGenerator_parity m) u).symm

theorem fullTranslation_mul (u v : FullCochain) :
    fullTranslation (u * v) = fullTranslation u * v + u * fullTranslation v :=
  fullTranslation_wedge u v

theorem fullTranslation_parity (u : FullCochain) :
    fullTranslation (fullParity u) = fullParity (fullTranslation u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    rw [fullParity_of_mem (full_single_mem s r), map_smul,
      fullParity_of_mem (fullTranslation_degree (full_single_mem s r))]
    rfl

theorem full_induction {P : FullCochain → Prop}
    (hzero : P 0) (hone : P fullOne)
    (hadd : ∀u v, P u → P v → P (u + v))
    (hsmul : ∀(r : ℂ) u, P u → P (r • u))
    (hgen : ∀a u, P u → P (fullWedge (fullGenerator a) u))
    (u : FullCochain) : P u :=
  FiniteExterior.induction_on FullMode.code hzero hone hadd hsmul hgen u

theorem full_algebra : IsGradedDifferentialSuperalgebra FullCochain fullData where
  grading_internal := full_grading_internal
  one_mul := fullOne_wedge
  mul_one := fullWedge_one
  mul_assoc := fullWedge_assoc
  supercomm _ _ _ _ hu hv := full_supercomm hu hv
  one_degree := full_one_mem
  mul_degree _ _ _ _ hu hv := full_wedge_mem hu hv
  translation_degree d a hu := by
    rcases d with ⟨k, b, s⟩
    simpa [fullData, Degree.translate, Prod.add_def] using fullTranslation_degree hu
  translation_one := fullTranslation_one
  translation_mul := fullTranslation_wedge

end KhanSL2
