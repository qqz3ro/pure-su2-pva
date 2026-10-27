module

public import KhanSL2.Macdonald.StrongBridgeFixedRootAction
public import KhanSL2.Factorization.WeightedRootModelPowerSums
public import KhanSL2.Conditional.BGGAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The root model over the original coefficient ring in a fixed symmetric degree.
Only the equality of degree indices is transported; the action is the original
weighted characteristic-polynomial action on signed invariant polynomials. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel Conditional

/-- Identify coefficient rings along the actual equality of symmetric degrees. -/
def fixedRootRingEquiv (s : ℕ) (d : RootHomologyDegrees s) :
    CoefficientRing s ≃ₐ[ℂ] CoefficientRing (d.val.1+2*d.val.2) := by
  obtain ⟨⟨q,r⟩,hd⟩ := d
  have h : s=q+2*r := by omega
  cases h
  exact AlgEquiv.refl

/-- The original signed weighted polynomial module, with its fixed total degree retained. -/
def FixedSignedRootModel (s : ℕ) (d : RootHomologyDegrees s) : Type :=
  signedInvariantModule d.val.1 d.val.2

instance (s : ℕ) (d : RootHomologyDegrees s) : AddCommGroup (FixedSignedRootModel s d) :=
  inferInstanceAs (AddCommGroup (signedInvariantModule d.val.1 d.val.2))
instance (s : ℕ) (d : RootHomologyDegrees s) : Module ℂ (FixedSignedRootModel s d) :=
  inferInstanceAs (Module ℂ (signedInvariantModule d.val.1 d.val.2))
instance (s : ℕ) (d : RootHomologyDegrees s) :
    Module (CoefficientRing s) (FixedSignedRootModel s d) :=
  Module.compHom (signedInvariantModule d.val.1 d.val.2) (fixedRootRingEquiv s d).toRingHom

instance fixedSignedRoot_smulComm (s : ℕ) (d : RootHomologyDegrees s) :
    SMulCommClass ℂ (CoefficientRing s) (FixedSignedRootModel s d) where
  smul_comm c a p := smul_comm c (fixedRootRingEquiv s d a)
    (show signedInvariantModule d.val.1 d.val.2 from p)

instance fixedSignedRoot_scalarTower (s : ℕ) (d : RootHomologyDegrees s) :
    IsScalarTower ℂ (CoefficientRing s) (FixedSignedRootModel s d) where
  smul_assoc c a p := by
    change fixedRootRingEquiv s d (c • a) •
      (show signedInvariantModule d.val.1 d.val.2 from p) = c • (fixedRootRingEquiv s d a •
        (show signedInvariantModule d.val.1 d.val.2 from p))
    rw [map_smul,smul_assoc]

/-- The concrete polynomial product equivalence in each retained degree. -/
def fixedSignedRootBlockEquiv (s : ℕ) (d : RootHomologyDegrees s) :
    RootHomologyModel d.val.1 d.val.2 ≃ₗ[ℂ] FixedSignedRootModel s d :=
  rootHomologyModelEquiv d.val.1 d.val.2

/-- Preserve all bidegrees while using the original signed-invariant polynomial modules. -/
def fixedSignedRootEquiv (s : ℕ) :
    (⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2) ≃ₗ[ℂ]
      (⨁ d : RootHomologyDegrees s, FixedSignedRootModel s d) :=
  DFinsupp.mapRange.linearEquiv (fixedSignedRootBlockEquiv s)

/-- Exact independent power-sum action in every original weighted polynomial block. -/
theorem fixedSignedRootBlockEquiv_powerSum (s : ℕ) (d : RootHomologyDegrees s)
    (i : Fin s) (x : RootHomologyModel d.val.1 d.val.2) :
    fixedSignedRootBlockEquiv s d (rootHomologyPowerSumEnd (i.val+1) d.val.1 d.val.2 x) =
      coefficientCoordinates s (MvPolynomial.X i) • fixedSignedRootBlockEquiv s d x := by
  obtain ⟨⟨q,r⟩,hd⟩ := d
  have hs : s=q+2*r := by omega
  cases hs
  change rootHomologyModelEquiv q r (rootHomologyPowerSumEnd (i.val+1) q r x) =
    coefficientCoordinates (q+2*r) (MvPolynomial.X i) • rootHomologyModelEquiv q r x
  simp only [coefficientCoordinates,AlgEquiv.trans_apply,Modules.powerSumAlgEquiv_X]
  exact rootHomologyModelEquiv_powerSum_scalar (i.val+1) q r x

/-- The sum of weighted power sums is the original coefficient scalar on the whole fixed model. -/
theorem fixedSignedRootEquiv_powerSum (s : ℕ) (i : Fin s)
    (x : ⨁ d : RootHomologyDegrees s, RootHomologyModel d.val.1 d.val.2) :
    fixedSignedRootEquiv s (fixedRootPowerSumEnd (i.val+1) s x) =
      coefficientCoordinates s (MvPolynomial.X i) • fixedSignedRootEquiv s x := by
  apply DFinsupp.ext
  intro d
  change fixedSignedRootBlockEquiv s d (rootHomologyPowerSumEnd (i.val+1) d.val.1 d.val.2 (x d)) =
    coefficientCoordinates s (MvPolynomial.X i) • fixedSignedRootBlockEquiv s d (x d)
  exact fixedSignedRootBlockEquiv_powerSum s d i (x d)

end KhanSL2.Macdonald
