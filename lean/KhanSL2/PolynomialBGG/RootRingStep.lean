module

public import KhanSL2.Depth.SourceModules
public import Mathlib.RingTheory.AdjoinRoot

@[expose] public section

/-! # Adjoining one root of the universal monic polynomial

The coefficient algebra of a monic polynomial of degree n together with one
labelled root is the monogenic extension of the coefficient algebra in degree
n+1. This is the induction step in Artin freeness.
-/

noncomputable section
namespace KhanSL2.PolynomialBGG

open Polynomial

/-- The universal monic polynomial in lower-coefficient coordinates. -/
def universalMonic (n : ℕ) : Polynomial (Depth.RB n) :=
  Depth.monicOf n MvPolynomial.X

theorem universalMonic_monic (n : ℕ) : (universalMonic n).Monic :=
  Depth.monicOf_monic n _

@[simp] theorem universalMonic_natDegree (n : ℕ) : (universalMonic n).natDegree = n :=
  Depth.natDegree_monicOf n _

@[simp] theorem universalMonic_coeff (n : ℕ) (i : Fin n) :
    (universalMonic n).coeff i = MvPolynomial.X i :=
  Depth.coeff_monicOf n _ i

/-- Coefficients of a monic factor, together with a distinguished root. -/
abbrev RootStep (n : ℕ) : Type := Polynomial (Depth.RB n)


/-- The monic degree-n factor over the ring with the distinguished root. -/
def stepFactor (n : ℕ) : Polynomial (RootStep n) :=
  (universalMonic n).map Polynomial.C

/-- Multiply the degree-n factor by the distinguished linear factor. -/
def stepProduct (n : ℕ) : Polynomial (RootStep n) :=
  (Polynomial.X - Polynomial.C (Polynomial.X : RootStep n)) * stepFactor n

theorem stepFactor_monic (n : ℕ) : (stepFactor n).Monic :=
  (universalMonic_monic n).map _

@[simp] theorem stepFactor_natDegree (n : ℕ) : (stepFactor n).natDegree = n := by
  rw [stepFactor, (universalMonic_monic n).natDegree_map, universalMonic_natDegree]

theorem stepProduct_monic (n : ℕ) : (stepProduct n).Monic :=
  (monic_X_sub_C _).mul (stepFactor_monic n)

@[simp] theorem stepProduct_natDegree (n : ℕ) : (stepProduct n).natDegree = n + 1 := by
  rw [stepProduct, (monic_X_sub_C _).natDegree_mul (stepFactor_monic n),
    natDegree_X_sub_C, stepFactor_natDegree, Nat.add_comm]

/-- The lower coefficients of the product define the scalar action. -/
def stepMap (n : ℕ) : Depth.RB (n + 1) →ₐ[ℂ] RootStep n :=
  MvPolynomial.aeval fun i => (stepProduct n).coeff i

@[simp] theorem stepMap_X (n : ℕ) (i : Fin (n + 1)) :
    stepMap n (MvPolynomial.X i) = (stepProduct n).coeff i :=
  MvPolynomial.aeval_X _ _

instance (n : ℕ) : Algebra (Depth.RB (n + 1)) (RootStep n) := (stepMap n).toAlgebra

theorem universalMonic_map_stepMap (n : ℕ) :
    (universalMonic (n + 1)).map (stepMap n).toRingHom = stepProduct n := by
  apply Depth.eq_of_monic_of_coeff_lt
    ((universalMonic_monic (n + 1)).map _) (stepProduct_monic n)
    ((universalMonic_monic (n + 1)).natDegree_map _ |>.trans (universalMonic_natDegree _))
    (stepProduct_natDegree n)
  intro k hk
  rw [Polynomial.coeff_map, universalMonic_coeff (n + 1) ⟨k, hk⟩]
  exact stepMap_X n ⟨k, hk⟩

theorem universalMonic_step_root (n : ℕ) :
    (universalMonic (n + 1)).eval₂ (stepMap n) (Polynomial.X : RootStep n) = 0 := by
  change (universalMonic (n + 1)).eval₂ (stepMap n).toRingHom Polynomial.X = 0
  rw [← Polynomial.eval_map, universalMonic_map_stepMap, stepProduct, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]

/-- Evaluation from the universal monogenic extension. -/
def stepFromAdjoin (n : ℕ) : AdjoinRoot (universalMonic (n + 1)) →ₐ[ℂ] RootStep n :=
  AdjoinRoot.liftAlgHom _ (stepMap n) Polynomial.X (universalMonic_step_root n)

instance (n : ℕ) : Nontrivial (AdjoinRoot (universalMonic (n + 1))) :=
  ⟨⟨0, 1, fun h => zero_ne_one (by simpa only [map_zero, map_one] using congrArg (stepFromAdjoin n) h)⟩⟩
/-- Remove the distinguished linear factor inside the monogenic extension. -/
def stepQuotient (n : ℕ) : Polynomial (AdjoinRoot (universalMonic (n + 1))) :=
  (universalMonic (n + 1)).map (AdjoinRoot.of _) /ₘ
    (Polynomial.X - Polynomial.C (AdjoinRoot.root _))

theorem stepQuotient_factorization (n : ℕ) :
    (Polynomial.X - Polynomial.C (AdjoinRoot.root (universalMonic (n + 1)))) *
      stepQuotient n = (universalMonic (n + 1)).map (AdjoinRoot.of _) :=
  Polynomial.mul_divByMonic_eq_iff_isRoot.mpr (AdjoinRoot.isRoot_root _)

theorem stepQuotient_monic (n : ℕ) : (stepQuotient n).Monic :=
  Monic.of_mul_monic_left (monic_X_sub_C _)
    ((stepQuotient_factorization n).symm ▸ (universalMonic_monic (n + 1)).map _)

@[simp] theorem stepQuotient_natDegree (n : ℕ) : (stepQuotient n).natDegree = n := by
  have h := congrArg Polynomial.natDegree (stepQuotient_factorization n)
  rw [(monic_X_sub_C _).natDegree_mul (stepQuotient_monic n), natDegree_X_sub_C,
    (universalMonic_monic (n + 1)).natDegree_map, universalMonic_natDegree] at h
  omega

/-- Recover the coefficients of the remaining factor. -/
def stepCoefficientToAdjoin (n : ℕ) :
    Depth.RB n →ₐ[ℂ] AdjoinRoot (universalMonic (n + 1)) :=
  MvPolynomial.aeval fun i => (stepQuotient n).coeff i

/-- The inverse coordinate map, adjoining the distinguished root. -/
def stepToAdjoin (n : ℕ) : RootStep n →ₐ[ℂ] AdjoinRoot (universalMonic (n + 1)) :=
  Polynomial.eval₂AlgHom (stepCoefficientToAdjoin n) (AdjoinRoot.root _) (fun _ => Commute.all _ _)


@[simp] theorem stepFromAdjoin_of (n : ℕ) (a : Depth.RB (n + 1)) :
    stepFromAdjoin n (AdjoinRoot.of _ a) = stepMap n a :=
  AdjoinRoot.liftAlgHom_of _ _ _ _ a

@[simp] theorem stepFromAdjoin_root (n : ℕ) :
    stepFromAdjoin n (AdjoinRoot.root _) = (Polynomial.X : RootStep n) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] theorem stepToAdjoin_C (n : ℕ) (a : Depth.RB n) :
    stepToAdjoin n (Polynomial.C a) = stepCoefficientToAdjoin n a :=
  Polynomial.eval₂_C _ _

@[simp] theorem stepToAdjoin_X (n : ℕ) :
    stepToAdjoin n (Polynomial.X : RootStep n) = AdjoinRoot.root _ :=
  Polynomial.eval₂_X _ _

theorem stepQuotient_map_fromAdjoin (n : ℕ) :
    (stepQuotient n).map (stepFromAdjoin n).toRingHom = stepFactor n := by
  rw [stepQuotient, Polynomial.map_divByMonic _ (monic_X_sub_C _), Polynomial.map_map]
  have hc : (stepFromAdjoin n).toRingHom.comp (AdjoinRoot.of (universalMonic (n + 1))) =
      (stepMap n).toRingHom := by
    apply RingHom.ext
    intro a
    exact stepFromAdjoin_of n a
  rw [hc, universalMonic_map_stepMap]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, stepFromAdjoin_root]
  rw [show (stepFromAdjoin n).toRingHom (AdjoinRoot.root (universalMonic (n + 1))) =
    (Polynomial.X : RootStep n) from stepFromAdjoin_root n, stepProduct]
  exact Polynomial.mul_divByMonic_cancel_left _ (monic_X_sub_C _)

theorem stepFactor_map_toAdjoin (n : ℕ) :
    (stepFactor n).map (stepToAdjoin n).toRingHom = stepQuotient n := by
  rw [stepFactor, Polynomial.map_map]
  apply Depth.eq_of_monic_of_coeff_lt
    ((universalMonic_monic n).map _) (stepQuotient_monic n)
    (by rw [(universalMonic_monic n).natDegree_map, universalMonic_natDegree])
    (stepQuotient_natDegree n)
  intro k hk
  rw [Polynomial.coeff_map, universalMonic_coeff n ⟨k, hk⟩]
  change stepToAdjoin n (Polynomial.C (MvPolynomial.X ⟨k, hk⟩)) = _
  rw [stepToAdjoin_C]
  exact MvPolynomial.aeval_X _ _

theorem stepFromAdjoin_comp_stepToAdjoin (n : ℕ) :
    (stepFromAdjoin n).comp (stepToAdjoin n) = AlgHom.id ℂ (RootStep n) := by
  apply Polynomial.algHom_ext'
  · apply MvPolynomial.algHom_ext
    intro i
    change stepFromAdjoin n (stepToAdjoin n (Polynomial.C (MvPolynomial.X i))) =
      Polynomial.C (MvPolynomial.X i)
    rw [stepToAdjoin_C]
    rw [show stepCoefficientToAdjoin n (MvPolynomial.X i) = (stepQuotient n).coeff i from
      MvPolynomial.aeval_X _ _]
    change (stepFromAdjoin n).toRingHom ((stepQuotient n).coeff i) = _
    rw [← Polynomial.coeff_map, stepQuotient_map_fromAdjoin]
    rw [stepFactor, Polynomial.coeff_map, universalMonic_coeff]
  · change stepFromAdjoin n (stepToAdjoin n Polynomial.X) = Polynomial.X
    rw [stepToAdjoin_X, stepFromAdjoin_root]

theorem stepToAdjoin_stepMap (n : ℕ) (a : Depth.RB (n + 1)) :
    stepToAdjoin n (stepMap n a) = AdjoinRoot.of _ a := by
  have h : (stepToAdjoin n).comp (stepMap n) = AdjoinRoot.ofAlgHom ℂ (universalMonic (n + 1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change stepToAdjoin n (stepMap n (MvPolynomial.X i)) = AdjoinRoot.of _ (MvPolynomial.X i)
    rw [stepMap_X]
    change (stepToAdjoin n).toRingHom ((stepProduct n).coeff i) = _
    rw [← Polynomial.coeff_map]
    rw [stepProduct, Polynomial.map_mul]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, stepToAdjoin_X]
    rw [show (stepToAdjoin n).toRingHom (Polynomial.X : RootStep n) =
      AdjoinRoot.root (universalMonic (n + 1)) from stepToAdjoin_X n]
    rw [stepFactor_map_toAdjoin, stepQuotient_factorization, Polynomial.coeff_map,
      universalMonic_coeff]
  exact AlgHom.congr_fun h a

theorem stepToAdjoin_comp_stepFromAdjoin (n : ℕ) :
    (stepToAdjoin n).comp (stepFromAdjoin n) =
      AlgHom.id ℂ (AdjoinRoot (universalMonic (n + 1))) := by
  apply AdjoinRoot.algHom_ext'
  · apply AlgHom.ext
    intro a
    change stepToAdjoin n (stepFromAdjoin n (AdjoinRoot.of _ a)) = AdjoinRoot.of _ a
    rw [stepFromAdjoin_of, stepToAdjoin_stepMap]
  · change stepToAdjoin n (stepFromAdjoin n (AdjoinRoot.root _)) = AdjoinRoot.root _
    rw [stepFromAdjoin_root, stepToAdjoin_X]

/-- The one-root extension is precisely the universal monogenic extension. -/
def rootStepEquivAdjoin (n : ℕ) :
    RootStep n ≃ₐ[Depth.RB (n + 1)] AdjoinRoot (universalMonic (n + 1)) :=
  { AlgEquiv.ofAlgHom (stepToAdjoin n) (stepFromAdjoin n)
      (stepToAdjoin_comp_stepFromAdjoin n) (stepFromAdjoin_comp_stepToAdjoin n) with
    commutes' a := stepToAdjoin_stepMap n a }

/-- Adjoining one root is a free extension of rank n+1. -/
theorem rootStep_free (n : ℕ) : Module.Free (Depth.RB (n + 1)) (RootStep n) := by
  have := (universalMonic_monic (n + 1)).free_adjoinRoot
  exact Module.Free.of_equiv (rootStepEquivAdjoin n).symm.toLinearEquiv

end KhanSL2.PolynomialBGG

