module

public import KhanSL2.Modules.SourceDualTaylor

@[expose] public section

/-! The restricted source dual is the concrete polynomial module in each valid sector. -/

noncomputable section
set_option maxHeartbeats 1000000
open scoped DirectSum BigOperators

namespace KhanSL2.Modules

open MvPolynomial

/-- Taking a homogeneous polynomial component preserves the actual `J`. -/
def jHomogeneousComponent (r s N : ℕ) : J r s →ₗ[ℂ] J r s where
  toFun q := ⟨homogeneousComponent N (q : Polynomial r s), homogeneousComponent_mem_J r s N q⟩
  map_add' q t := Subtype.ext ((homogeneousComponent N).map_add (q : Polynomial r s) t)
  map_smul' c q := Subtype.ext ((homogeneousComponent N).map_smul c (q : Polynomial r s))

@[simp] theorem jHomogeneousComponent_coe (r s N : ℕ) (q : J r s) :
    (jHomogeneousComponent r s N q : Polynomial r s) = homogeneousComponent N (q : Polynomial r s) :=
  rfl

theorem sum_jHomogeneousComponent (r s : ℕ) (q : J r s) :
    ∑ N ∈ Finset.range ((q : Polynomial r s).totalDegree + 1), jHomogeneousComponent r s N q = q := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, jHomogeneousComponent_coe]
  exact sum_homogeneousComponent (q : Polynomial r s)

/-- The polynomial realization of a single spin piece of the restricted source dual. -/
def sourceDualPolynomialPiece (r s : ℕ) (spin : ℤ) :
    Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) spin)) →ₗ[ℂ] J r s :=
  if sectorSpinBase r s ≤ spin then
    (taylorToJ r s (spin - sectorSpinBase r s).toNat).comp
      (extendSourceDual (Current.kDegree r (r + 3 * s) spin))
  else 0

@[simp] theorem sourceDualPolynomialPiece_sector (r s N : ℕ) :
    sourceDualPolynomialPiece r s (sectorSpinBase r s + N) = sourceDualTaylor r s N := by
  simp [sourceDualPolynomialPiece, sourceDualTaylor]

@[simp] theorem sourceDualPolynomialPiece_below (r s : ℕ) (spin : ℤ)
    (h : spin < sectorSpinBase r s) : sourceDualPolynomialPiece r s spin = 0 := by
  simp [sourceDualPolynomialPiece, not_le.mpr h]

/-- The polynomial model of the restricted, rather than unrestricted, source dual. -/
def sourceDualPolynomial (r s : ℕ) : sourceDualTotal (r + 3 * s) r →ₗ[ℂ] J r s :=
  DirectSum.toModule ℂ ℤ (J r s) (sourceDualPolynomialPiece r s)

@[simp] theorem sourceDualPolynomial_lof (r s : ℕ) (spin : ℤ)
    (ell : Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) spin))) :
    sourceDualPolynomial r s (DirectSum.lof ℂ ℤ
      (fun t => Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) t))) spin ell) =
        sourceDualPolynomialPiece r s spin ell :=
  DirectSum.toModule_lof ℂ (φ := sourceDualPolynomialPiece r s) spin ell

@[simp] theorem sourceDualPolynomial_of (r s : ℕ) (spin : ℤ)
    (ell : Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) spin))) :
    sourceDualPolynomial r s (DirectSum.of
      (fun t => Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) t))) spin ell) =
        sourceDualPolynomialPiece r s spin ell :=
  sourceDualPolynomial_lof r s spin ell
/-- Polynomial homogeneous projection extracts precisely one source spin. -/
theorem jHomogeneousComponent_sourceDualPolynomialPiece (r s N : ℕ) (spin : ℤ)
    (ell : Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) spin))) :
    jHomogeneousComponent r s N (sourceDualPolynomialPiece r s spin ell) =
      if spin = sectorSpinBase r s + N then sourceDualPolynomialPiece r s spin ell else 0 := by
  by_cases hs : sectorSpinBase r s ≤ spin
  · obtain ⟨M, hspin⟩ : ∃ M : ℕ, spin = sectorSpinBase r s + M :=
      ⟨(spin - sectorSpinBase r s).toNat, by omega⟩
    subst spin
    rw [sourceDualPolynomialPiece_sector]
    apply Subtype.ext
    change homogeneousComponent N (sourceDualTaylor r s M ell : Polynomial r s) = _
    rw [homogeneousComponent_of_mem (sourceDualTaylor_homogeneous r s M ell)]
    by_cases hNM : N = M
    · subst N; simp
    · have hspin : sectorSpinBase r s + (M : ℤ) ≠ sectorSpinBase r s + N := by omega
      simp [hNM, hspin]
  · rw [sourceDualPolynomialPiece_below r s spin (lt_of_not_ge hs)]
    simp

/-- The assembled polynomial determines each homogeneous source functional. -/
theorem jHomogeneousComponent_sourceDualPolynomial (r s N : ℕ)
    (x : sourceDualTotal (r + 3 * s) r) :
    jHomogeneousComponent r s N (sourceDualPolynomial r s x) =
      sourceDualTaylor r s N (x (sectorSpinBase r s + N)) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of spin ell =>
    rw [sourceDualPolynomial_of, jHomogeneousComponent_sourceDualPolynomialPiece]
    by_cases h : spin = sectorSpinBase r s + N
    · subst spin
      simp [DirectSum.lof_eq_of]
    · simp [h, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add x y hx hy =>
    simp only [map_add, DirectSum.add_apply]
    rw [hx, hy]

/-- Distinct source spins cannot cancel in the polynomial model. -/
theorem sourceDualPolynomial_injective (r s : ℕ) : Function.Injective (sourceDualPolynomial r s) := by
  intro x y h
  apply DFinsupp.ext
  intro spin
  by_cases hs : sectorSpinBase r s ≤ spin
  · obtain ⟨N, hspin⟩ : ∃ N : ℕ, spin = sectorSpinBase r s + N :=
      ⟨(spin - sectorSpinBase r s).toNat, by omega⟩
    subst spin
    apply sourceDualTaylor_injective r s N
    simpa only [jHomogeneousComponent_sourceDualPolynomial] using
      congrArg (jHomogeneousComponent r s N) h
  · have hbot := source_piece_eq_bot_below r s spin (lt_of_not_ge hs)
    let : Subsingleton (Source.piece (Current.kDegree r (r + 3 * s) spin)) :=
      Submodule.subsingleton_iff_eq_bot.mpr hbot
    exact Subsingleton.elim _ _

/-- Every polynomial in `J` has finitely many homogeneous pieces, each realized above. -/
theorem sourceDualPolynomial_surjective (r s : ℕ) : Function.Surjective (sourceDualPolynomial r s) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro q _
  rw [← sum_jHomogeneousComponent r s q]
  apply Submodule.sum_mem
  intro N _
  obtain ⟨ell, hell⟩ := sourceDualTaylor_surjective_homogeneous r s N
    (jHomogeneousComponent r s N q) (homogeneousComponent_isHomogeneous N (q : Polynomial r s))
  refine ⟨DirectSum.lof ℂ ℤ
    (fun spin => Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) spin)))
      (sectorSpinBase r s + N) ell, ?_⟩
  rw [sourceDualPolynomial_lof, sourceDualPolynomialPiece_sector, hell]

/-- The genuine restricted source dual is the concrete discriminant polynomial module. -/
def sourceDualPolynomialEquiv (r s : ℕ) : sourceDualTotal (r + 3 * s) r ≃ₗ[ℂ] J r s :=
  LinearEquiv.ofBijective (sourceDualPolynomial r s)
    ⟨sourceDualPolynomial_injective r s, sourceDualPolynomial_surjective r s⟩

/-- The specific comparison is the transpose of `phi` followed by the proved polynomial model. -/
theorem sourceDualPolynomial_comp_psiTotal (r s : ℕ) :
    (sourceDualPolynomial r s).comp (psiTotal (r + 3 * s) r) = psiPolynomial r s := by
  apply DirectSum.linearMap_ext
  intro spin
  apply LinearMap.ext
  intro k
  simp only [LinearMap.comp_apply, psiTotal_lof, sourceDualPolynomial_lof, psiPolynomial_lof]
  by_cases hs : sectorSpinBase r s ≤ spin
  · obtain ⟨N, hspin⟩ : ∃ N : ℕ, spin = sectorSpinBase r s + N :=
      ⟨(spin - sectorSpinBase r s).toNat, by omega⟩
    subst spin
    exact (LinearMap.congr_fun (sourceDualPolynomialPiece_sector r s N)
      (Current.psiK r (r + 3 * s) (sectorSpinBase r s + N) k)).trans
        ((sourceDualTaylor_psiK r s N k).trans
          (LinearMap.congr_fun (psiPolynomialPiece_sector r s N) k).symm)
  · exact (LinearMap.congr_fun (sourceDualPolynomialPiece_below r s spin (lt_of_not_ge hs))
      (Current.psiK r (r + 3 * s) spin k)).trans
        (LinearMap.congr_fun (psiPolynomialPiece_below r s spin (lt_of_not_ge hs)) k).symm

end KhanSL2.Modules