module

public import KhanSL2.BGG.PositiveHarmonicPieces

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual harmonic space is the internal direct sum of its degree-p
subrepresentations. Every vector has finite homogeneous support. -/

noncomputable section
open scoped BigOperators DirectSum
namespace KhanSL2.BGG.PositiveCE

/-- The homogeneous projection restricts to the actual harmonic kernel. -/
def harmonicBidegreeProjection (q : ℕ × ℕ) : Module.End ℂ Harmonic where
  toFun u := ⟨BasisGrading.projection bidegree q (u : Cochain), by
    have h := BasisGrading.projection_linearMap bidegree laplacian id Function.injective_id
      (fun k w hw => (mem_bidegree_piece k _).mpr
        (laplacian_mem_piece ((mem_bidegree_piece k w).mp hw))) q (u : Cochain)
    have hu : laplacian (u : Cochain) = 0 := u.property
    rw [hu, map_zero] at h
    exact h.symm⟩
  map_add' u v := Subtype.ext (map_add (BasisGrading.projection bidegree q)
    (u : Cochain) (v : Cochain))
  map_smul' r u := Subtype.ext (map_smul (BasisGrading.projection bidegree q) r (u : Cochain))

@[simp] theorem harmonicBidegreeProjection_coe (q : ℕ × ℕ) (u : Harmonic) :
    (harmonicBidegreeProjection q u : Cochain) =
      BasisGrading.projection bidegree q (u : Cochain) := rfl

theorem harmonicBidegreeProjection_mem (q : ℕ × ℕ) (u : Harmonic) :
    harmonicBidegreeProjection q u ∈ harmonicDegree q.1 := by
  have hp := (mem_bidegree_piece q _).mp (BasisGrading.projection_mem bidegree q (u : Cochain))
  exact fun s hs => (hp hs).1

/-- Every harmonic vector is the finite sum of its homogeneous harmonic projections. -/
theorem harmonic_sum_bidegreeProjection (u : Harmonic) :
    (∑ q ∈ (BasisGrading.coaction bidegree (u : Cochain)).support,
      harmonicBidegreeProjection q u) = u := by
  apply Subtype.ext
  change Harmonic.subtype (∑ q ∈ (BasisGrading.coaction bidegree (u : Cochain)).support,
    harmonicBidegreeProjection q u) = (u : Cochain)
  rw [map_sum]
  exact BasisGrading.sum_projection bidegree (u : Cochain)

/-- The actual harmonic degree summands span the entire harmonic space. -/
theorem harmonicDegree_iSup_eq_top :
    (⨆ p : ℕ, (harmonicDegree p).toSubmodule) = ⊤ := by
  apply eq_top_iff.mpr
  intro u _
  rw [← harmonic_sum_bidegreeProjection u]
  apply Submodule.sum_mem
  intro q _
  exact Submodule.mem_iSup_of_mem q.1 (harmonicBidegreeProjection_mem q u)

/-- The ambient homogeneous coaction extracts each component of the sum map. -/
theorem harmonicDegree_coaction_directSum
    (v : ⨁ p : ℕ, (harmonicDegree p).toSubmodule) (p : ℕ) :
    BasisGrading.coaction (fun s : Finset Mode => s.card)
      ((DirectSum.coeLinearMap (fun q : ℕ => (harmonicDegree q).toSubmodule) v : Harmonic) : Cochain) p =
        (((v p : (harmonicDegree p).toSubmodule) : Harmonic) : Cochain) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of q v =>
    have hv : ((v : Harmonic) : Cochain) ∈
        BasisGrading.piece (fun s : Finset Mode => s.card) q := v.property
    rw [DirectSum.coeLinearMap_of, BasisGrading.coaction_of_mem _ hv]
    by_cases h : q = p
    · subst p
      simp
    · rw [Finsupp.single_eq_of_ne' h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
      rfl
  | add v w hv hw =>
    simp only [map_add, Submodule.coe_add, DirectSum.add_apply, Finsupp.add_apply, hv, hw]
/-- The harmonic space is the actual internal direct sum of its degree subrepresentations. -/
theorem harmonicDegree_isInternal :
    DirectSum.IsInternal (fun p : ℕ => (harmonicDegree p).toSubmodule) := by
  change Function.Bijective (DirectSum.coeLinearMap (fun p : ℕ => (harmonicDegree p).toSubmodule))
  constructor
  · intro v w hvw
    apply DFinsupp.ext
    intro p
    apply Subtype.ext
    apply Subtype.ext
    rw [← harmonicDegree_coaction_directSum v p, ← harmonicDegree_coaction_directSum w p, hvw]
  · apply LinearMap.range_eq_top.mp
    rw [DirectSum.range_coeLinearMap, harmonicDegree_iSup_eq_top]

/-- Explicit linear decomposition by degree, given by summing homogeneous harmonics. -/
def harmonicDegreeLinearEquiv : (⨁ p : ℕ, (harmonicDegree p).toSubmodule) ≃ₗ[ℂ] Harmonic :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (fun p : ℕ => (harmonicDegree p).toSubmodule))
    harmonicDegree_isInternal

end KhanSL2.BGG.PositiveCE
