module

public import KhanSL2.Modules.CoefficientHomology
public import KhanSL2.Modules.PowerSumCoordinates
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

@[expose] public section

/-!
# The symmetric coefficient ring acts on actual relative homology

The first `B` power sums are polynomial coordinates on the genuine ring
`R B` of symmetric polynomials. We evaluate these coordinates at the
commuting operators induced by multiplication by powers of `z` on the
coefficient factors. Thus the action is constructed on CE chains and
then descended to homology; it is independent of the map `ψ`.
-/

noncomputable section

namespace KhanSL2.Modules

/-- Evaluate a polynomial at a commuting family in a possibly noncommutative algebra. -/
def commutingPolynomialEval {ι A : Type*} [Ring A] [Algebra ℂ A]
    (f : ι → A) (hf : ∀ i j, Commute (f i) (f j)) : MvPolynomial ι ℂ →ₐ[ℂ] A := by
  let C : Subalgebra ℂ A := Algebra.adjoin ℂ (Set.range f)
  letI : IsMulCommutative C := Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hf i j)
  letI : CommRing C := { (inferInstance : Ring C) with mul_comm := mul_comm' }
  exact C.val.comp (MvPolynomial.aeval fun i => (⟨f i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : C))

@[simp] theorem commutingPolynomialEval_X {ι A : Type*} [Ring A] [Algebra ℂ A]
    (f : ι → A) (hf : ∀ i j, Commute (f i) (f j)) (i : ι) :
    commutingPolynomialEval f hf (MvPolynomial.X i) = f i := by
  simp [commutingPolynomialEval]

/-- The actual coefficient action in power-sum coordinates. -/
def coefficientPolynomialAction (B p : ℕ) :
    MvPolynomial (Fin B) ℂ →ₐ[ℂ] Module.End ℂ (KTotal B p) :=
  commutingPolynomialEval (fun i : Fin B => coefficientTotalPower (i.val + 1) B p)
    (fun i j => coefficientTotalPower_commute (i.val + 1) (j.val + 1) B p)

/-- The action of the symmetric root ring on actual relative CE homology. -/
def coefficientAction (B p : ℕ) : R B →ₐ[ℂ] Module.End ℂ (KTotal B p) :=
  (coefficientPolynomialAction B p).comp (powerSumAlgEquiv B).symm.toAlgHom

/-- The module structure comes from the genuine coefficient-chain operators. -/
instance coefficientModule (B p : ℕ) : Module (R B) (KTotal B p) :=
  Module.compHom (KTotal B p) (coefficientAction B p).toRingHom

@[simp] theorem coefficient_smul_eq (B p : ℕ) (r : R B) (x : KTotal B p) :
    r • x = coefficientAction B p r x := rfl

/-- Identifying formula for every polynomial generator of `R B`. -/
theorem coefficientAction_powerSum (B p : ℕ) (i : Fin B) :
    coefficientAction B p (powerSum B (i.val + 1)) =
      coefficientTotalPower (i.val + 1) B p := by
  calc
    coefficientAction B p (powerSum B (i.val + 1)) =
        coefficientPolynomialAction B p (MvPolynomial.X i) :=
      congrArg (coefficientPolynomialAction B p) (powerSumAlgEquiv_symm_powerSum B i)
    _ = _ := commutingPolynomialEval_X _ _ i

/-- A power sum acts by the explicitly constructed coefficient shift on homology. -/
theorem powerSum_smul (B p : ℕ) (i : Fin B) (x : KTotal B p) :
    powerSum B (i.val + 1) • x = coefficientTotalPower (i.val + 1) B p x := by
  exact LinearMap.congr_fun (coefficientAction_powerSum B p i) x

instance coefficientSMulCommClass (B p : ℕ) : SMulCommClass ℂ (R B) (KTotal B p) where
  smul_comm c r x := (map_smul (coefficientAction B p r) c x).symm

instance coefficientIsScalarTower (B p : ℕ) : IsScalarTower ℂ (R B) (KTotal B p) where
  smul_assoc c r x := by
    change coefficientAction B p (c • r) x = c • coefficientAction B p r x
    exact LinearMap.congr_fun ((coefficientAction B p).toLinearMap.map_smul c r) x

/-- Polynomial algebra coordinates reduce module-linearity to their variables. -/
theorem polynomialCoordinates_intertwines {ι A M V : Type*}
    [CommRing A] [Algebra ℂ A]
    [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
    [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]
    (e : MvPolynomial ι ℂ ≃ₐ[ℂ] A) (f : M →ₗ[ℂ] V)
    (hf : ∀ i x, f (e (MvPolynomial.X i) • x) = e (MvPolynomial.X i) • f x)
    (r : A) (x : M) : f (r • x) = r • f x := by
  have h : ∀ (q : MvPolynomial ι ℂ) (y : M), f (e q • y) = e q • f y := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      intro y
      have hc : e (MvPolynomial.C c) = algebraMap ℂ A c := e.commutes c
      rw [hc, algebraMap_smul, algebraMap_smul, map_smul]
    | add q t hq ht =>
      intro y
      simp only [map_add, add_smul, hq, ht]
    | mul_X q i hq =>
      intro y
      simp only [map_mul, mul_smul]
      rw [hq, hf]
  simpa only [AlgEquiv.apply_symm_apply] using h (e.symm r) x

/-- Intertwining the first `B` actual coefficient shifts implies full symmetric-ring linearity. -/
theorem coefficientAction_intertwines (B p : ℕ) {V : Type*}
    [AddCommGroup V] [Module ℂ V] [Module (R B) V] [IsScalarTower ℂ (R B) V]
    (f : KTotal B p →ₗ[ℂ] V)
    (hf : ∀ (i : Fin B) (x : KTotal B p),
      f (coefficientTotalPower (i.val + 1) B p x) = powerSum B (i.val + 1) • f x)
    (r : R B) (x : KTotal B p) : f (r • x) = r • f x := by
  apply polynomialCoordinates_intertwines (powerSumAlgEquiv B) f _ r x
  intro i y
  calc
    f (powerSumAlgEquiv B (MvPolynomial.X i) • y) =
        f (powerSum B (i.val + 1) • y) :=
      congrArg (fun a : R B => f (a • y)) (powerSumAlgEquiv_X B i)
    _ = f (coefficientTotalPower (i.val + 1) B p y) :=
      congrArg f (powerSum_smul B p i y)
    _ = powerSum B (i.val + 1) • f y := hf i y
    _ = powerSumAlgEquiv B (MvPolynomial.X i) • f y :=
      congrArg (fun a : R B => a • f y) (powerSumAlgEquiv_X B i).symm

end KhanSL2.Modules