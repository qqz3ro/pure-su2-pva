module

public import KhanSL2.Modules.SourceDualPieces
public import KhanSL2.Injectivity.SelectedCycles
public import KhanSL2.Injectivity.TaylorChainComparison

@[expose] public section

/-! The Taylor realization identifies homogeneous source duals with homogeneous parts of `J`. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2.Modules

open SourceDual MvPolynomial

/-- Restrict an ambient source functional to the actual homogeneous piece. -/
def restrictSourceDual (d : Degree) : Module.Dual ℂ Source →ₗ[ℂ] Module.Dual ℂ (Source.piece d) :=
  LinearMap.lcomp ℂ ℂ (Source.piece d).subtype

/-- The Taylor map on a genuine homogeneous source dual. -/
def sourceDualTaylor (r s N : ℕ) :
    Module.Dual ℂ (Source.piece (Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N)))
      →ₗ[ℂ] J r s :=
  (taylorToJ r s N).comp
    (extendSourceDual (Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N)))

/-- Canonical extension does not change any Taylor coefficient in the chosen sector. -/
theorem taylor_extend_restrict (r s N : ℕ) (ell : Module.Dual ℂ Source) :
    taylorPolynomial r s N
      (extendSourceDual (Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N))
        (restrictSourceDual _ ell)) = taylorPolynomial r s N ell := by
  classical
  unfold taylorPolynomial
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : indexWeight a = N
  · rw [if_pos ha, if_pos ha]
    congr 2
    change ell (sourceProjection _ (taylorJetPiece r s N a ha) : Source) =
      ell (taylorJetPiece r s N a ha : Source)
    rw [sourceProjection_coe]
  · rw [if_neg ha, if_neg ha]

@[simp] theorem sourceDualTaylor_restrict (r s N : ℕ) (ell : Module.Dual ℂ Source) :
    sourceDualTaylor r s N (restrictSourceDual _ ell) = taylorToJ r s N ell :=
  Subtype.ext (taylor_extend_restrict r s N ell)

theorem sourceDualTaylor_homogeneous (r s N : ℕ)
    (ell : Module.Dual ℂ (Source.piece
      (Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N)))) :
    (sourceDualTaylor r s N ell : Polynomial r s).IsHomogeneous N :=
  taylorPolynomial_homogeneous r s N _

/-- Taylor coefficients determine a functional on the entire source piece. -/
theorem sourceDualTaylor_injective (r s N : ℕ) : Function.Injective (sourceDualTaylor r s N) := by
  intro ell m h
  ext a
  have ha : (a : Source) ∈ Source.sector r s N := by
    rw [← source_piece_eq_sector, sectorDegree_eq_kDegree]
    exact a.property
  have heq := eq_on_sector_of_taylorPolynomial_eq
    (extendSourceDual _ ell) (extendSourceDual _ m) (congrArg Subtype.val h) ha
  simpa only [extendSourceDual_coe] using heq

/-- Every explicit spanning cycle polynomial is realized by a genuine source functional. -/
theorem cyclePolynomial_taylor_realization (r s N : ℕ) (e : Fin r → ℕ)
    (q : MvPolynomial (Fin s) ℂ) (hq : q.IsSymmetric) :
    ∃ ell : Module.Dual ℂ Source,
      taylorPolynomial r s N ell = homogeneousComponent N (Injectivity.cyclePolynomial r s e q) := by
  let f := Injectivity.descendCartanFunctional
    (FiniteExterior.coefficientPairing (Injectivity.Cartan.selectedCycleChain r s e q))
    (Injectivity.Cartan.selectedCycleChain_closed r s e q)
  let c : ℂ := (-2 : ℂ) ^ s * Injectivity.Cartan.selectedCycleScalar r s
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num))
    (Injectivity.Cartan.selectedCycleScalar_ne_zero r s)
  have hf : taylorPolynomial r s N (f.comp phi) =
      c • homogeneousComponent N (Injectivity.cyclePolynomial r s e q) := by
    rw [Injectivity.taylor_descended_chainPolynomial,
      Injectivity.Cartan.chainPolynomial_selectedCycle r s e q hq, map_smul, smul_smul]
  refine ⟨c⁻¹ • (f.comp phi), ?_⟩
  change taylorPolynomialLinear r s N (c⁻¹ • (f.comp phi)) = _
  rw [map_smul, taylorPolynomialLinear_apply, hf, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- Realization extends linearly to the entire actual cycle-polynomial span. -/
theorem cyclePolynomialSpan_taylor_realization (r s N : ℕ) (q : Polynomial r s)
    (hq : q ∈ Injectivity.cyclePolynomialSpan r s) :
    ∃ ell : Module.Dual ℂ Source, taylorPolynomial r s N ell = homogeneousComponent N q := by
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨⟨e, ⟨q, hq⟩⟩, rfl⟩ := hq
    exact cyclePolynomial_taylor_realization r s N e q hq
  | zero => exact ⟨0, by simp [← taylorPolynomialLinear_apply]⟩
  | add q t _ _ hq ht =>
    obtain ⟨ell, hell⟩ := hq
    obtain ⟨m, hm⟩ := ht
    refine ⟨ell + m, ?_⟩
    change taylorPolynomialLinear r s N (ell + m) = _
    rw [map_add, taylorPolynomialLinear_apply, taylorPolynomialLinear_apply, hell, hm, map_add]
  | smul c q _ hq =>
    obtain ⟨ell, hell⟩ := hq
    refine ⟨c • ell, ?_⟩
    change taylorPolynomialLinear r s N (c • ell) = _
    rw [map_smul, taylorPolynomialLinear_apply, hell, map_smul]

/-- Every homogeneous component of an actual polynomial in `J` is a Taylor polynomial. -/
theorem j_taylor_realization (r s N : ℕ) (q : J r s) :
    ∃ ell : Module.Dual ℂ Source,
      taylorPolynomial r s N ell = homogeneousComponent N (q : Polynomial r s) := by
  obtain ⟨a, ha⟩ := q.property
  apply cyclePolynomialSpan_taylor_realization
  rw [ha]
  exact Injectivity.discriminant_mul_mem_cyclePolynomialSpan r s a a.property

/-- The homogeneous image is all of the corresponding homogeneous part of `J`. -/
theorem sourceDualTaylor_surjective_homogeneous (r s N : ℕ) (q : J r s)
    (hq : (q : Polynomial r s).IsHomogeneous N) :
    ∃ ell, sourceDualTaylor r s N ell = q := by
  obtain ⟨ell, hell⟩ := j_taylor_realization r s N q
  refine ⟨restrictSourceDual _ ell, ?_⟩
  apply Subtype.ext
  rw [sourceDualTaylor_restrict, taylorToJ_coe, hell, homogeneousComponent_eq_self hq]

/-- The actual polynomial `J` is closed under taking homogeneous components. -/
theorem homogeneousComponent_mem_J (r s N : ℕ) (q : J r s) :
    homogeneousComponent N (q : Polynomial r s) ∈ JSubmodule r s := by
  obtain ⟨ell, hell⟩ := j_taylor_realization r s N q
  rw [← hell]
  exact taylorPolynomial_mem_J r s N ell

/-- In every genuine source degree, the polynomial comparison is the Taylor map of `psiK`. -/
theorem sourceDualTaylor_psiK (r s N : ℕ)
    (k : Current.K r (r + 3 * s) (sectorSpinBase r s + N)) :
    sourceDualTaylor r s N (Current.psiK r (r + 3 * s) (sectorSpinBase r s + N) k) =
      psiPolynomialSector r s N k := by
  have h : Current.psiK r (r + 3 * s) (sectorSpinBase r s + N) k =
      restrictSourceDual _ (sourceFunctional r (r + 3 * s) (sectorSpinBase r s + N) k) := by
    ext a
    rfl
  exact (congrArg (sourceDualTaylor r s N) h).trans
    (sourceDualTaylor_restrict r s N
      (sourceFunctional r (r + 3 * s) (sectorSpinBase r s + N) k))

end KhanSL2.Modules