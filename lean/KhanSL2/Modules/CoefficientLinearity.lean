module

public import KhanSL2.Modules.SourceDualShift
public import KhanSL2.Modules.CoefficientAction
public import KhanSL2.Modules.CoefficientJetPairing

@[expose] public section

/-!
# Coefficient-ring linearity of the specified polynomial comparison

The chain-defined coefficient shifts lower ordinary source jets by falling
factorials under the pairing. Taylor normalization turns this into
multiplication by the weighted power sums. The resulting `R B`-linear map is
exactly the previously defined `psiB`.
-/

noncomputable section
open scoped DirectSum BigOperators

namespace KhanSL2.Modules

open SourceDual

private theorem descending_sum_if {r s : ℕ} (m : ℕ)
    (ell : Module.Dual ℂ Source) (d : Variables r s →₀ ℕ) :
    (∑ i, (wordRootWeight i * ((d i).descFactorial m : ℂ)) *
      ell (exponentMonomial (d - Finsupp.single i m))) =
    ∑ i, if m ≤ d i then sourceRootWeight i * ((d i).descFactorial m : ℂ) *
      ell (exponentMonomial (d - Finsupp.single i m)) else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : m ≤ d i
  · rw [if_pos hi]
    rfl
  · rw [if_neg hi, Nat.descFactorial_of_lt (Nat.lt_of_not_ge hi)]
    simp

/-- The chain/jet pairing identity with zero falling-factorial cases explicit. -/
private theorem sourceFunctional_coefficientKPower_if (m p B : ℕ) (spin : ℤ)
    (k : Current.K p B spin) {r s : ℕ} (d : Variables r s →₀ ℕ) :
    sourceFunctional p B (spin + m) (coefficientKPower m p B spin k) (exponentMonomial d) =
      ∑ i, if m ≤ d i then sourceRootWeight i * ((d i).descFactorial m : ℂ) *
        sourceFunctional p B spin k (exponentMonomial (d - Finsupp.single i m)) else 0 :=
  (sourceFunctional_coefficientKPower m p B spin k d).trans
    (descending_sum_if m (sourceFunctional p B spin k) d)

/-- Above the sector base, the spinwise comparison is its specified Taylor polynomial. -/
theorem psiPolynomialPiece_coe_of_le (r s : ℕ) (spin : ℤ)
    (h : sectorSpinBase r s ≤ spin) (k : Current.K r (r + 3 * s) spin) :
    (psiPolynomialPiece r s spin k : Polynomial r s) =
      taylorPolynomial r s (spin - sectorSpinBase r s).toNat
        (sourceFunctional r (r + 3 * s) spin k) := by
  simp only [psiPolynomialPiece, if_pos h, LinearMap.comp_apply, taylorToJ_coe]

private def taylorAtSpin (r s : ℕ) (spin : ℤ) (ell : Module.Dual ℂ Source) : Polynomial r s :=
  if sectorSpinBase r s ≤ spin then
    taylorPolynomial r s (spin - sectorSpinBase r s).toNat ell else 0

private theorem psiPolynomialPiece_coe (r s : ℕ) (spin : ℤ)
    (k : Current.K r (r + 3 * s) spin) :
    (psiPolynomialPiece r s spin k : Polynomial r s) =
      taylorAtSpin r s spin (sourceFunctional r (r + 3 * s) spin k) := by
  by_cases h : sectorSpinBase r s ≤ spin
  · exact (psiPolynomialPiece_coe_of_le r s spin h k).trans (if_pos h).symm
  · exact (congrArg (fun q : J r s => q.val)
      (LinearMap.congr_fun (psiPolynomialPiece_below r s spin (lt_of_not_ge h)) k)).trans
        (if_neg h).symm

private theorem taylorAtSpin_shift (r s m : ℕ) (spin : ℤ)
    (ell ell' : Module.Dual ℂ Source)
    (h : ∀ d : Variables r s →₀ ℕ,
      ell' (exponentMonomial d) = ∑ i, if m ≤ d i then
        sourceRootWeight i * ((d i).descFactorial m : ℂ) *
          ell (exponentMonomial (d - Finsupp.single i m)) else 0) :
    taylorAtSpin r s (spin + m) ell' =
      (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) * taylorAtSpin r s spin ell := by
  by_cases hs : sectorSpinBase r s ≤ spin
  · have hsm : sectorSpinBase r s ≤ spin + (m : ℤ) := by omega
    have hN : (spin + (m : ℤ) - sectorSpinBase r s).toNat =
        (spin - sectorSpinBase r s).toNat + m := by omega
    simp only [taylorAtSpin, if_pos hs, if_pos hsm, hN]
    exact (taylor_jet_lowering r s (spin - sectorSpinBase r s).toNat m
      sourceRootWeight ell ell' (fun d _ => h d)).trans
        (congrArg (fun q : Polynomial r s => q * taylorPolynomial r s
          (spin - sectorSpinBase r s).toNat ell) (jetShiftPolynomial_sourceRootWeight r s m))
  · by_cases hsm : sectorSpinBase r s ≤ spin + (m : ℤ)
    · simp only [taylorAtSpin, if_pos hsm, if_neg hs, mul_zero]
      exact taylor_jet_lowering_below r s (spin + (m : ℤ) - sectorSpinBase r s).toNat m
        sourceRootWeight ell ell' (by omega) (fun d _ => h d)
    · simp only [taylorAtSpin, if_neg hs, if_neg hsm, mul_zero]

/-- Every spin piece intertwines the actual coefficient shift and the weighted-root power sum. -/
theorem psiPolynomialPiece_coefficientKPower (r s m : ℕ) (spin : ℤ)
    (k : Current.K r (r + 3 * s) spin) :
    psiPolynomialPiece r s (spin + m) (coefficientKPower m r (r + 3 * s) spin k) =
      powerSum (r + 3 * s) m • psiPolynomialPiece r s spin k := by
  apply Subtype.ext
  calc
    _ = taylorAtSpin r s (spin + m)
        (sourceFunctional r (r + 3 * s) (spin + m)
          (coefficientKPower m r (r + 3 * s) spin k)) :=
      psiPolynomialPiece_coe r s (spin + m) (coefficientKPower m r (r + 3 * s) spin k)
    _ = (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) *
        taylorAtSpin r s spin (sourceFunctional r (r + 3 * s) spin k) :=
      taylorAtSpin_shift r s m spin _ _
        (fun d => sourceFunctional_coefficientKPower_if m r (r + 3 * s) spin k d)
    _ = (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) *
        (psiPolynomialPiece r s spin k : Polynomial r s) :=
      congrArg (fun q : Polynomial r s => (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) * q)
        (psiPolynomialPiece_coe r s spin k).symm
    _ = _ := (j_smul_coe r s (powerSum (r + 3 * s) m) (psiPolynomialPiece r s spin k)).symm

/-- Direct-sum assembly preserves the coefficient-shift identity. -/
theorem psiPolynomial_coefficientTotalPower (r s m : ℕ) (x : KTotal (r + 3 * s) r) :
    psiPolynomial r s (coefficientTotalPower m (r + 3 * s) r x) =
      powerSum (r + 3 * s) m • psiPolynomial r s x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of spin k =>
    calc
      _ = psiPolynomial r s (DirectSum.lof ℂ ℤ (fun t => Current.K r (r + 3 * s) t)
          (spin + m) (coefficientKPower m r (r + 3 * s) spin k)) :=
        congrArg (psiPolynomial r s) (coefficientTotalPower_lof m (r + 3 * s) r spin k)
      _ = psiPolynomialPiece r s (spin + m) (coefficientKPower m r (r + 3 * s) spin k) :=
        psiPolynomial_lof r s (spin + m) (coefficientKPower m r (r + 3 * s) spin k)
      _ = powerSum (r + 3 * s) m • psiPolynomialPiece r s spin k :=
        psiPolynomialPiece_coefficientKPower r s m spin k
      _ = _ := congrArg (fun q : J r s => powerSum (r + 3 * s) m • q)
        (psiPolynomial_lof r s spin k).symm
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- Reindexing the coefficient degree preserves the actual coefficient operators. -/
theorem kTotalCast_coefficientTotalPower {B C : ℕ} (h : B = C) (p m : ℕ) (x : KTotal B p) :
    kTotalCast h p (coefficientTotalPower m B p x) =
      coefficientTotalPower m C p (kTotalCast h p x) := by
  subst C
  rfl

@[simp] theorem ringCast_powerSum {B C : ℕ} (h : B = C) (m : ℕ) :
    ringCast h (powerSum B m) = powerSum C m := by
  subst C
  rfl

/-- The valid-sector identification respects the original coefficient action. -/
theorem jToJB_smul (B p : ℕ) (h : ValidSector B p) (a : R B)
    (q : J p (sectorS B p)) :
    jToJB B p h (ringCast h a • q) = a • jToJB B p h q := by
  apply Subtype.ext
  change (nu p (sectorS B p) (ringCast h a) : Polynomial p (sectorS B p)) * q.val =
    (nuB B p a : Polynomial p (sectorS B p)) * q.val
  simp only [nuB, dif_pos h, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]

/-- The existing comparison intertwines every natural coefficient power shift. -/
theorem psiB_coefficientTotalPower (m B p : ℕ) (x : KTotal B p) :
    psiB B p (coefficientTotalPower m B p x) = powerSum B m • psiB B p x := by
  by_cases h : ValidSector B p
  · calc
      _ = jToJB B p h (psiPolynomial p (sectorS B p)
          (kTotalCast h p (coefficientTotalPower m B p x))) :=
        psiB_of_valid B p h (coefficientTotalPower m B p x)
      _ = jToJB B p h (psiPolynomial p (sectorS B p)
          (coefficientTotalPower m (p + 3 * sectorS B p) p (kTotalCast h p x))) :=
        congrArg (fun y : KTotal (p + 3 * sectorS B p) p =>
          jToJB B p h (psiPolynomial p (sectorS B p) y))
            (kTotalCast_coefficientTotalPower h p m x)
      _ = jToJB B p h (powerSum (p + 3 * sectorS B p) m •
          psiPolynomial p (sectorS B p) (kTotalCast h p x)) :=
        congrArg (jToJB B p h)
          (psiPolynomial_coefficientTotalPower p (sectorS B p) m (kTotalCast h p x))
      _ = jToJB B p h (ringCast h (powerSum B m) •
          psiPolynomial p (sectorS B p) (kTotalCast h p x)) :=
        congrArg (fun a : R (p + 3 * sectorS B p) =>
          jToJB B p h (a • psiPolynomial p (sectorS B p) (kTotalCast h p x)))
            (ringCast_powerSum h m).symm
      _ = powerSum B m • jToJB B p h
          (psiPolynomial p (sectorS B p) (kTotalCast h p x)) :=
        jToJB_smul B p h (powerSum B m) (psiPolynomial p (sectorS B p) (kTotalCast h p x))
      _ = _ := congrArg (fun q : JB B p => powerSum B m • q) (psiB_of_valid B p h x).symm
  · exact (jb_eq_zero_of_invalid h _).trans (jb_eq_zero_of_invalid h _).symm

/-- Coefficient-ring linearity from the first `B` power-sum generators. -/
theorem psiB_smul (B p : ℕ) (a : R B) (x : KTotal B p) :
    psiB B p (a • x) = a • psiB B p x :=
  coefficientAction_intertwines B p (V := JB B p) (psiB B p)
    (fun i x => psiB_coefficientTotalPower (i.val + 1) B p x) a x

/-- The specified polynomial comparison, with proved coefficient-ring linearity. -/
def psiBLinear (B p : ℕ) : KTotal B p →ₗ[R B] JB B p where
  toFun := psiB B p
  map_add' := (psiB B p).map_add
  map_smul' := psiB_smul B p

@[simp] theorem psiBLinear_apply (B p : ℕ) (x : KTotal B p) :
    psiBLinear B p x = psiB B p x := rfl

/-- Forgetting the extra linearity gives exactly the previously specified map. -/
theorem psiBLinear_restrictScalars (B p : ℕ) :
    (psiBLinear B p).restrictScalars ℂ = psiB B p := by
  apply LinearMap.ext
  intro x
  rfl

/-- The actual coefficient-linear comparison is surjective. -/
theorem psiBLinear_surjective (B p : ℕ) : Function.Surjective (psiBLinear B p) :=
  psiB_surjective B p

end KhanSL2.Modules
