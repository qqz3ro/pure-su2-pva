module

public import KhanSL2.Modules.GradedAssembly
public import KhanSL2.Modules.PolynomialModels
public import KhanSL2.Injectivity.TaylorLinear
public import KhanSL2.Injectivity.SourcePolynomialSpan

@[expose] public section

/-!
# The specified polynomial comparison

A homology class pairs with the image under the original map `phi` of any source
class. Its finite Taylor polynomial satisfies the source relations, hence lies
in the concrete discriminant module `J`. Summing these maps over spin defines
the polynomial comparison on the actual relative homology.

The maps here are complex-linear. No identification of the full restricted
source dual with `J`, and no coefficient-ring linearity on homology, is assumed.
-/

noncomputable section
open scoped DirectSum

namespace KhanSL2.Modules

open SourceDual

/-- The actual chain-homology model used by the cohomology pairing. -/
def kChainEquiv (p B : ℕ) (spin : ℤ) :
    Current.K p B spin ≃ₗ[ℂ] ChainHomology (Current.kDegree p B spin) :=
  (Current.relHomologyEquivComplex (Current.kDegree p B spin)).symm.trans
    (Current.relHomologyEquiv (Current.kDegree p B spin))

/-- Pair a homology class with `phi` on the whole source; this uses no arbitrary
extension of a functional on a homogeneous piece. -/
def sourceFunctional (p B : ℕ) (spin : ℤ) :
    Current.K p B spin →ₗ[ℂ] Module.Dual ℂ Source :=
  ((cohomologyToDual (Current.kDegree p B spin)).comp phi).flip.comp
    (kChainEquiv p B spin).toLinearMap

@[simp] theorem sourceFunctional_apply (p B : ℕ) (spin : ℤ)
    (k : Current.K p B spin) (a : Source) :
    sourceFunctional p B spin k a =
      cohomologyToDual (Current.kDegree p B spin) (phi a) (kChainEquiv p B spin k) := rfl

/-- Restriction is exactly the previously defined transpose of `phi`. -/
theorem sourceFunctional_restrict (p B : ℕ) (spin : ℤ)
    (k : Current.K p B spin) (a : Source.piece (Current.kDegree p B spin)) :
    sourceFunctional p B spin k a = Current.psiK p B spin k a := rfl

/-- Source relations prove the Taylor polynomial belongs to the actual `J`. -/
theorem taylorPolynomial_mem_J (r s N : ℕ) (ell : Module.Dual ℂ Source) :
    taylorPolynomial r s N ell ∈ JSubmodule r s := by
  apply (mem_JSubmodule_iff_dvd_character _).mpr
  exact ⟨exists_discriminant_quotient r s N ell,
    taylorPolynomial_block_character r s N ell⟩

/-- The polynomial realization map, retaining its proved `J` membership. -/
def taylorToJ (r s N : ℕ) : Module.Dual ℂ Source →ₗ[ℂ] J r s where
  toFun ell := ⟨taylorPolynomial r s N ell, taylorPolynomial_mem_J r s N ell⟩
  map_add' ell m := Subtype.ext ((taylorPolynomialLinear r s N).map_add ell m)
  map_smul' c ell := Subtype.ext ((taylorPolynomialLinear r s N).map_smul c ell)

@[simp] theorem taylorToJ_coe (r s N : ℕ) (ell : Module.Dual ℂ Source) :
    (taylorToJ r s N ell : Polynomial r s) = taylorPolynomial r s N ell := rfl

/-- Spin at the lowest Taylor degree of the `(r,s)` source sector. -/
def sectorSpinBase (r s : ℕ) : ℤ := (2 * r + 3 * s : ℕ)

/-- The homogeneous comparison at nonnegative Taylor degree `N`. -/
def psiPolynomialSector (r s N : ℕ) :
    Current.K r (r + 3 * s) (sectorSpinBase r s + N) →ₗ[ℂ] J r s :=
  (taylorToJ r s N).comp (sourceFunctional r (r + 3 * s) (sectorSpinBase r s + N))

/-- Every coefficient explicitly uses the original map `phi` and chain pairing. -/
theorem psiPolynomialSector_coeff (r s N : ℕ)
    (k : Current.K r (r + 3 * s) (sectorSpinBase r s + N))
    (d : Variables r s →₀ ℕ) :
    (psiPolynomialSector r s N k : Polynomial r s).coeff d =
      if d.degree = N then
        cohomologyToDual (Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N))
          (phi (exponentMonomial d))
          (kChainEquiv r (r + 3 * s) (sectorSpinBase r s + N) k) /
            exponentFactorial d
      else 0 :=
  coeff_taylorPolynomial_all r s N
    (sourceFunctional r (r + 3 * s) (sectorSpinBase r s + N) k) d

/-- The spinwise map; there is no Taylor polynomial in negative degree. -/
def psiPolynomialPiece (r s : ℕ) (spin : ℤ) :
    Current.K r (r + 3 * s) spin →ₗ[ℂ] J r s :=
  if sectorSpinBase r s ≤ spin then
    (taylorToJ r s (spin - sectorSpinBase r s).toNat).comp
      (sourceFunctional r (r + 3 * s) spin)
  else 0

@[simp] theorem psiPolynomialPiece_below (r s : ℕ) (spin : ℤ)
    (h : spin < sectorSpinBase r s) : psiPolynomialPiece r s spin = 0 := by
  simp [psiPolynomialPiece, not_le.mpr h]

@[simp] theorem psiPolynomialPiece_sector (r s N : ℕ) :
    psiPolynomialPiece r s (sectorSpinBase r s + N) = psiPolynomialSector r s N := by
  simp [psiPolynomialPiece, psiPolynomialSector]

/-- The specified polynomial comparison, assembled over all spins. -/
def psiPolynomial (r s : ℕ) : KTotal (r + 3 * s) r →ₗ[ℂ] J r s :=
  DirectSum.toModule ℂ ℤ (J r s) (psiPolynomialPiece r s)

/-- Each homogeneous inclusion has exactly the prescribed Taylor image. -/
@[simp] theorem psiPolynomial_lof (r s : ℕ) (spin : ℤ)
    (k : Current.K r (r + 3 * s) spin) :
    psiPolynomial r s
      (DirectSum.lof ℂ ℤ (fun t => Current.K r (r + 3 * s) t) spin k) =
        psiPolynomialPiece r s spin k :=
  DirectSum.toModule_lof ℂ spin k

/-- Source sector grading agrees with the relative-homology indexing. -/
theorem sectorDegree_eq_kDegree (r s N : ℕ) :
    Source.sectorDegree r s N =
      Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N) := by
  ext <;> simp [Source.sectorDegree, Current.kDegree, sectorSpinBase]
  ring

/-- A labelled Taylor jet is a genuine element of the matching source piece. -/
def taylorJetPiece (r s N : ℕ) (a : TaylorIndex r s N) (ha : indexWeight a = N) :
    Source.piece (Current.kDegree r (r + 3 * s) (sectorSpinBase r s + N)) :=
  ⟨Source.jetMonomial (xIndices a) (yIndices a), by
    rw [← sectorDegree_eq_kDegree]
    have hsum : (xIndices a).sum + (yIndices a).sum = N := ha
    simpa only [xIndices_length, yIndices_length, hsum] using
      Source.jetMonomial_mem_piece (xIndices a) (yIndices a)⟩

/-- The polynomial comparison has exactly the Taylor coefficients of the
previously specified `psiK`, evaluated on actual homogeneous source classes. -/
theorem psiPolynomialSector_coeff_psiK (r s N : ℕ)
    (k : Current.K r (r + 3 * s) (sectorSpinBase r s + N))
    (a : TaylorIndex r s N) (ha : indexWeight a = N) :
    (psiPolynomialSector r s N k : Polynomial r s).coeff (exponent a) =
      Current.psiK r (r + 3 * s) (sectorSpinBase r s + N) k
        (taylorJetPiece r s N a ha) / jetFactorial a :=
  coeff_taylorPolynomial
    (sourceFunctional r (r + 3 * s) (sectorSpinBase r s + N) k) a ha

/-- The spinwise image is a homogeneous polynomial in exactly the expected degree. -/
theorem psiPolynomialSector_homogeneous (r s N : ℕ)
    (k : Current.K r (r + 3 * s) (sectorSpinBase r s + N)) :
    (psiPolynomialSector r s N k : Polynomial r s).IsHomogeneous N :=
  taylorPolynomial_homogeneous r s N
    (sourceFunctional r (r + 3 * s) (sectorSpinBase r s + N) k)
end KhanSL2.Modules