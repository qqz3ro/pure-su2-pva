module

public import KhanSL2.Modules.PolynomialMap

@[expose] public section

/-! Canonical projections and the actual source pieces used by the polynomial dual model. -/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Modules

/-- Assemble the established internal source grading. -/
def sourceAssemble : (⨁ d : Degree, Source.piece d) ≃ₗ[ℂ] Source :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap Source.piece) Source.grading_internal

/-- Canonical projection to a homogeneous source piece. -/
def sourceProjection (d : Degree) : Source →ₗ[ℂ] Source.piece d :=
  (DirectSum.component ℂ Degree (fun d => ↥(Source.piece d)) d).comp sourceAssemble.symm.toLinearMap

@[simp] theorem sourceAssemble_lof (d : Degree) (a : Source.piece d) :
    sourceAssemble (DirectSum.lof ℂ Degree (fun d => ↥(Source.piece d)) d a) = a :=
  DirectSum.coeLinearMap_of Source.piece d a

@[simp] theorem sourceProjection_coe (d : Degree) (a : Source.piece d) :
    sourceProjection d (a : Source) = a := by
  have h : sourceAssemble.symm (a : Source) = DirectSum.lof ℂ Degree (fun d => ↥(Source.piece d)) d a := by
    apply sourceAssemble.injective
    rw [LinearEquiv.apply_symm_apply, sourceAssemble_lof]
  change DirectSum.component ℂ Degree (fun d => ↥(Source.piece d)) d (sourceAssemble.symm a) = a
  rw [h, DirectSum.component.lof_self]

/-- Extension by the canonical homogeneous projection. -/
def extendSourceDual (d : Degree) : Module.Dual ℂ (Source.piece d) →ₗ[ℂ] Module.Dual ℂ Source :=
  LinearMap.lcomp ℂ ℂ (sourceProjection d)

@[simp] theorem extendSourceDual_apply (d : Degree) (ell : Module.Dual ℂ (Source.piece d))
    (a : Source) : extendSourceDual d ell a = ell (sourceProjection d a) := rfl

@[simp] theorem extendSourceDual_coe (d : Degree) (ell : Module.Dual ℂ (Source.piece d))
    (a : Source.piece d) : extendSourceDual d ell a = ell a := by
  rw [extendSourceDual_apply, sourceProjection_coe]

/-- Assemble the independently established finer sector grading. -/
def sourceSectorAssemble :
    (⨁ t : Source.SectorIndex, Source.indexedSector t) ≃ₗ[ℂ] Source :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap Source.indexedSector) Source.sector_grading_internal

/-- At a source sector degree, the full homogeneous piece is exactly that sector. -/
theorem source_piece_eq_sector (r s N : ℕ) :
    Source.piece (Source.sectorDegree r s N) = Source.sector r s N := by
  apply le_antisymm
  · intro a ha
    let v := sourceSectorAssemble.symm a
    have hv : DirectSum.coeLinearMap Source.indexedSector v = a :=
      sourceSectorAssemble.apply_symm_apply a
    have h := Source.coaction_indexedSector_coe v (r, s, N)
    rw [hv, Source.coaction_of_mem ha] at h
    have heq : a = (v (r, s, N) : Source) := by simpa using h
    rw [heq]
    exact (v (r, s, N)).property
  · exact Source.sector_le_piece r s N

/-- The source grading has no support outside the explicitly enumerated sectors. -/
theorem source_coaction_unsupported (d : Degree)
    (hd : ∀ t : Source.SectorIndex, Source.sectorDegree t.1 t.2.1 t.2.2 ≠ d)
    (a : Source) : (Source.coaction a).coeff d = 0 := by
  obtain ⟨v, rfl⟩ := sourceSectorAssemble.surjective a
  change (Source.coaction (DirectSum.coeLinearMap Source.indexedSector v)).coeff d = 0
  induction v using DirectSum.induction_on with
  | zero => simp
  | of t a =>
    rw [DirectSum.coeLinearMap_of,
      Source.coaction_of_mem (Source.sector_le_piece t.1 t.2.1 t.2.2 a.property)]
    exact Finsupp.single_eq_of_ne (hd t).symm
  | add v w hv hw =>
    simp only [map_add]
    change (Source.coaction (DirectSum.coeLinearMap Source.indexedSector v)).coeff d +
      (Source.coaction (DirectSum.coeLinearMap Source.indexedSector w)).coeff d = 0
    rw [hv, hw, add_zero]

/-- Unsupported homogeneous source pieces are zero, without a presentation-basis assumption. -/
theorem source_piece_eq_bot_of_unsupported (d : Degree)
    (hd : ∀ t : Source.SectorIndex, Source.sectorDegree t.1 t.2.1 t.2.2 ≠ d) :
    Source.piece d = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  have h := source_coaction_unsupported d hd a
  rw [Source.coaction_of_mem ha] at h
  simpa using h

/-- Equality of source and homology grading indices determines the sector. -/
theorem kDegree_eq_sector_iff (p B : ℕ) (spin : ℤ) (r s N : ℕ) :
    Current.kDegree p B spin = Source.sectorDegree r s N ↔
      r = p ∧ B = p + 3 * s ∧ spin = sectorSpinBase p s + N := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg (fun d : Degree => d.2.1) h
    have h₃ := congrArg (fun d : Degree => d.2.2) h
    simp only [Current.kDegree, Source.sectorDegree, Prod.fst, Prod.snd, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] at h₁ h₂ h₃
    have hr : r = p := by omega
    subst r
    refine ⟨rfl, ?_, ?_⟩
    · omega
    · simpa [sectorSpinBase] using h₃
  · rintro ⟨hr, hB, hspin⟩
    subst r
    subst B
    subst spin
    exact (sectorDegree_eq_kDegree p s N).symm

/-- No source sector exists at an invalid coefficient/form-degree pair. -/
theorem source_piece_eq_bot_of_invalid (B p : ℕ) (spin : ℤ) (h : ¬ValidSector B p) :
    Source.piece (Current.kDegree p B spin) = ⊥ := by
  apply source_piece_eq_bot_of_unsupported
  rintro ⟨r, s, N⟩ heq
  have hs := ((kDegree_eq_sector_iff p B spin r s N).mp heq.symm).2.1
  exact h ((validSector_iff B p).mpr ⟨s, hs⟩)

/-- At fixed `(r,s)`, source spin starts at `2*r+3*s`. -/
theorem source_piece_eq_bot_below (r s : ℕ) (spin : ℤ) (h : spin < sectorSpinBase r s) :
    Source.piece (Current.kDegree r (r + 3 * s) spin) = ⊥ := by
  apply source_piece_eq_bot_of_unsupported
  rintro ⟨r', s', N⟩ heq
  obtain ⟨hr, hB, hspin⟩ := (kDegree_eq_sector_iff r (r + 3 * s) spin r' s' N).mp heq.symm
  have hs : s' = s := by omega
  subst s'
  omega

end KhanSL2.Modules