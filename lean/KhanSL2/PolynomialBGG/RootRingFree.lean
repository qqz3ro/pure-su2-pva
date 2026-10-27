module

public import KhanSL2.PolynomialBGG.RootRingStep
public import KhanSL2.PolynomialBGG.RootRingCoordinates
public import KhanSL2.PolynomialBGG.RootRingBaseChange
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace KhanSL2.PolynomialBGG

open Polynomial

/-- Labelled roots of the remaining factor, together with one distinguished root. -/
def RootInduction (n : ℕ) : Type := Polynomial (LowerRootPolynomial n)

instance (n : ℕ) : CommRing (RootInduction n) :=
  inferInstanceAs (CommRing (Polynomial (LowerRootPolynomial n)))
instance (n : ℕ) : Algebra ℂ (RootInduction n) :=
  inferInstanceAs (Algebra ℂ (Polynomial (LowerRootPolynomial n)))

attribute [local instance] Polynomial.algebra

instance (n : ℕ) : Algebra (RootStep n) (RootInduction n) :=
  inferInstanceAs (Algebra (Polynomial (Depth.RB n)) (Polynomial (LowerRootPolynomial n)))

/-- The total lower coefficients after adjoining the distinguished root. -/
def rootInductionMap (n : ℕ) : Depth.RB (n+1) →ₐ[ℂ] RootInduction n :=
  (Polynomial.mapAlgHom (lowerRootMap n)).comp (stepMap n)

instance (n : ℕ) : Algebra (Depth.RB (n+1)) (RootInduction n) :=
  (rootInductionMap n).toAlgebra

instance (n : ℕ) : IsScalarTower (Depth.RB (n+1)) (RootStep n) (RootInduction n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Evaluating the universal lower coefficients recovers the root product. -/
theorem universalMonic_map_lowerRootMap (n : ℕ) :
    (universalMonic n).map (lowerRootMap n).toRingHom = lowerRootChar n := by
  apply Depth.eq_of_monic_of_coeff_lt ((universalMonic_monic n).map _)
    (lowerRootChar_monic n)
    (by rw [(universalMonic_monic n).natDegree_map, universalMonic_natDegree])
    (lowerRootChar_natDegree n)
  intro k hk
  rw [Polynomial.coeff_map, universalMonic_coeff n ⟨k, hk⟩]
  exact lowerRootMap_X n ⟨k, hk⟩

/-- Separating the first labelled root separates one linear factor. -/
theorem lowerRootChar_finSucc (n : ℕ) :
    (lowerRootChar (n+1)).map (MvPolynomial.finSuccEquiv ℂ n).toRingHom =
      (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (LowerRootPolynomial n))) *
        (lowerRootChar n).map Polynomial.C := by
  change (∏ i : Fin (n+1),
      (Polynomial.X - Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin (n+1)) ℂ))).map
        (MvPolynomial.finSuccEquiv ℂ n).toRingHom =
    (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (MvPolynomial (Fin n) ℂ))) *
      (∏ i : Fin n,
        (Polynomial.X - Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))).map
          Polynomial.C
  have hz : (MvPolynomial.finSuccEquiv ℂ n).toRingEquiv.toRingHom (MvPolynomial.X 0) =
      (Polynomial.X : Polynomial (MvPolynomial (Fin n) ℂ)) :=
    MvPolynomial.finSuccEquiv_X_zero
  have hs (i : Fin n) :
      (MvPolynomial.finSuccEquiv ℂ n).toRingEquiv.toRingHom (MvPolynomial.X i.succ) =
        Polynomial.C (MvPolynomial.X i) := MvPolynomial.finSuccEquiv_X_succ
  simp only [Polynomial.map_prod, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Fin.prod_univ_succ, hz, hs]

/-- The remaining universal factor evaluates to the remaining labelled root product. -/
theorem stepFactor_map_lowerRootMap (n : ℕ) :
    (stepFactor n).map (Polynomial.mapRingHom (lowerRootMap n).toRingHom) =
      (lowerRootChar n).map Polynomial.C := by
  apply Polynomial.ext
  intro k
  simp only [stepFactor, Polynomial.coeff_map]
  change Polynomial.map (lowerRootMap n).toRingHom
      (Polynomial.C ((universalMonic n).coeff k)) = _
  rw [Polynomial.map_C]
  have h := congrArg (fun q : Polynomial (LowerRootPolynomial n) => q.coeff k)
    (universalMonic_map_lowerRootMap n)
  rw [Polynomial.coeff_map] at h
  rw [h]

/-- Both presentations have exactly the same total lower coefficients. -/
theorem stepProduct_map_lowerRootMap (n : ℕ) :
    (stepProduct n).map (Polynomial.mapRingHom (lowerRootMap n).toRingHom) =
      (lowerRootChar (n+1)).map (MvPolynomial.finSuccEquiv ℂ n).toRingHom := by
  rw [lowerRootChar_finSucc, stepProduct, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C]
  rw [show (Polynomial.mapRingHom (lowerRootMap n).toRingHom)
      (Polynomial.X : RootStep n) = Polynomial.X from Polynomial.map_X _]
  rw [stepFactor_map_lowerRootMap]

/-- The standard polynomial-variable equivalence preserves all coefficient scalars. -/
theorem lowerRootMap_finSucc (n : ℕ) (r : Depth.RB (n+1)) :
    MvPolynomial.finSuccEquiv ℂ n (lowerRootMap (n+1) r) = rootInductionMap n r := by
  have h : (MvPolynomial.finSuccEquiv ℂ n).toAlgHom.comp (lowerRootMap (n+1)) =
      rootInductionMap n := by
    apply MvPolynomial.algHom_ext
    intro i
    change MvPolynomial.finSuccEquiv ℂ n (lowerRootMap (n+1) (MvPolynomial.X i)) =
      rootInductionMap n (MvPolynomial.X i)
    calc
      MvPolynomial.finSuccEquiv ℂ n (lowerRootMap (n+1) (MvPolynomial.X i)) =
          MvPolynomial.finSuccEquiv ℂ n ((lowerRootChar (n+1)).coeff i) :=
        congrArg (fun z : LowerRootPolynomial (n+1) => MvPolynomial.finSuccEquiv ℂ n z)
          (lowerRootMap_X (n+1) i)
      _ = (Polynomial.mapRingHom (lowerRootMap n).toRingHom) ((stepProduct n).coeff i) := by
        have hcoeff := congrArg (fun q : Polynomial (Polynomial (LowerRootPolynomial n)) =>
          q.coeff i) (stepProduct_map_lowerRootMap n)
        simp only [Polynomial.coeff_map] at hcoeff
        exact hcoeff.symm
      _ = rootInductionMap n (MvPolynomial.X i) :=
        (congrArg (fun q : RootStep n => Polynomial.map (lowerRootMap n).toRingHom q)
          (stepMap_X n i)).symm
  exact AlgHom.congr_fun h r

/-- Splitting off the first root is an equivalence over the lower-coefficient ring. -/
def rootInductionEquiv (n : ℕ) :
    LowerRootPolynomial (n+1) ≃ₐ[Depth.RB (n+1)] RootInduction n where
  __ := (MvPolynomial.finSuccEquiv ℂ n).toRingEquiv
  commutes' r := lowerRootMap_finSucc n r

/-- Freeness ascends one labelled root via polynomial base change and a monic extension. -/
theorem rootInduction_free (n : ℕ)
    [Module.Free (Depth.RB n) (LowerRootPolynomial n)] :
    Module.Free (Depth.RB (n+1)) (RootInduction n) := by
  have : Module.Free (RootStep n) (RootInduction n) :=
    polynomial_free_of_free (Depth.RB n) (LowerRootPolynomial n)
  have := rootStep_free n
  exact Module.Free.trans (R := Depth.RB (n+1)) (S := RootStep n)

/-- In degree zero the coefficient map is the identity. -/
def lowerRootZeroEquiv : Depth.RB 0 ≃ₐ[Depth.RB 0] LowerRootPolynomial 0 where
  __ := RingEquiv.refl (Depth.RB 0)
  commutes' r := by
    change r = lowerRootMap 0 r
    have h : lowerRootMap 0 = AlgHom.id ℂ (Depth.RB 0) := by
      apply MvPolynomial.algHom_ext
      intro i
      exact Fin.elim0 i
    exact (AlgHom.congr_fun h r).symm

/-- Artin freeness of labelled-root polynomials in lower-coefficient coordinates. -/
theorem lowerRootPolynomial_free (n : ℕ) :
    Module.Free (Depth.RB n) (LowerRootPolynomial n) := by
  induction n with
  | zero => exact Module.Free.of_equiv lowerRootZeroEquiv.toLinearEquiv
  | succ n ih =>
    have := ih
    have := rootInduction_free n
    exact Module.Free.of_equiv (rootInductionEquiv n).symm.toLinearEquiv

/-- Labelled-root polynomials are free for the prescribed elementary-coordinate action. -/
theorem rootPolynomial_free (n : ℕ) : Module.Free (Depth.RB n) (RootPolynomial n) := by
  have := lowerRootPolynomial_free n
  exact rootPolynomial_free_of_lower n

instance (n : ℕ) : Module.Free (Depth.RB n) (RootPolynomial n) := rootPolynomial_free n

end KhanSL2.PolynomialBGG
