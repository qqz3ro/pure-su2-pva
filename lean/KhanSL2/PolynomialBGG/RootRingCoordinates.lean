module

public import KhanSL2.PolynomialBGG.RootRing
public import KhanSL2.Depth.SourceModules

@[expose] public section

/-! # Changing between elementary and lower-coefficient coordinates -/

noncomputable section
namespace KhanSL2.PolynomialBGG
open MvPolynomial

/-- Labelled roots, with scalars acting through the lower coefficients of their
monic product. The type synonym keeps this action distinct from elementary coordinates. -/
def LowerRootPolynomial (n : ℕ) : Type := MvPolynomial (Fin n) ℂ

instance (n : ℕ) : CommRing (LowerRootPolynomial n) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n) ℂ))
instance (n : ℕ) : Nontrivial (LowerRootPolynomial n) :=
  inferInstanceAs (Nontrivial (MvPolynomial (Fin n) ℂ))
instance (n : ℕ) : Algebra ℂ (LowerRootPolynomial n) :=
  inferInstanceAs (Algebra ℂ (MvPolynomial (Fin n) ℂ))

/-- The monic polynomial with the labelled variables as its roots. -/
def lowerRootChar (n : ℕ) : Polynomial (LowerRootPolynomial n) :=
  ∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X i : LowerRootPolynomial n))

theorem lowerRootChar_monic (n : ℕ) : (lowerRootChar n).Monic :=
  Depth.prod_X_sub_C_X_monic (Fin n)

@[simp] theorem lowerRootChar_natDegree (n : ℕ) : (lowerRootChar n).natDegree = n := by
  exact (Depth.natDegree_prod_X_sub_C_X (Fin n)).trans (Fintype.card_fin n)

/-- Coefficient variables act by the corresponding coefficients of the root product. -/
def lowerRootMap (n : ℕ) : Depth.RB n →ₐ[ℂ] LowerRootPolynomial n :=
  MvPolynomial.aeval fun i => (lowerRootChar n).coeff i

@[simp] theorem lowerRootMap_X (n : ℕ) (i : Fin n) :
    lowerRootMap n (MvPolynomial.X i) = (lowerRootChar n).coeff i :=
  MvPolynomial.aeval_X _ _

instance (n : ℕ) : Algebra (Depth.RB n) (LowerRootPolynomial n) :=
  (lowerRootMap n).toAlgebra

@[simp] theorem lowerRootPolynomial_algebraMap (n : ℕ) (r : Depth.RB n) :
    algebraMap (Depth.RB n) (LowerRootPolynomial n) r = lowerRootMap n r := rfl

theorem lowerRootPolynomial_smul (n : ℕ) (r : Depth.RB n) (q : LowerRootPolynomial n) :
    r • q = lowerRootMap n r * q := rfl

instance (n : ℕ) : IsScalarTower ℂ (Depth.RB n) (LowerRootPolynomial n) :=
  IsScalarTower.of_algebraMap_eq fun c => ((lowerRootMap n).commutes c).symm

/-- The underlying complex algebra remains the ordinary polynomial ring. -/
def lowerRootPolynomialEquiv (n : ℕ) :
    LowerRootPolynomial n ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := AlgEquiv.refl

/-- Lower coefficient k is (-1)^(n-k) times elementary coordinate n-k. -/
def rootCoordSign (n : ℕ) : Depth.RB n →ₐ[ℂ] Depth.RB n :=
  MvPolynomial.aeval fun k => (-1) ^ (n - (k : ℕ)) * MvPolynomial.X k.rev

/-- The inverse signed reversal. -/
def rootCoordSignInv (n : ℕ) : Depth.RB n →ₐ[ℂ] Depth.RB n :=
  MvPolynomial.aeval fun k => (-1) ^ ((k : ℕ) + 1) * MvPolynomial.X k.rev

theorem rootCoordSignInv_comp_sign (n : ℕ) :
    (rootCoordSignInv n).comp (rootCoordSign n) = AlgHom.id ℂ (Depth.RB n) := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [AlgHom.comp_apply, rootCoordSign, rootCoordSignInv, aeval_X, map_mul,
    map_pow, map_neg, map_one, Fin.rev_rev, AlgHom.id_apply, Fin.val_rev]
  rw [← mul_assoc, ← pow_add,
    show n - (k : ℕ) + (n - ((k : ℕ) + 1) + 1) = 2 * (n - k) by omega,
    pow_mul, neg_one_sq, one_pow, one_mul]

theorem rootCoordSign_comp_signInv (n : ℕ) :
    (rootCoordSign n).comp (rootCoordSignInv n) = AlgHom.id ℂ (Depth.RB n) := by
  apply MvPolynomial.algHom_ext
  intro k
  simp only [AlgHom.comp_apply, rootCoordSign, rootCoordSignInv, aeval_X, map_mul,
    map_pow, map_neg, map_one, Fin.rev_rev, AlgHom.id_apply, Fin.val_rev]
  rw [← mul_assoc, ← pow_add,
    show (k : ℕ) + 1 + (n - (n - ((k : ℕ) + 1))) = 2 * ((k : ℕ) + 1) by omega,
    pow_mul, neg_one_sq, one_pow, one_mul]

/-- Signed reversal is an automorphism of the coefficient algebra. -/
def rootCoordEquiv (n : ℕ) : Depth.RB n ≃ₐ[ℂ] Depth.RB n :=
  AlgEquiv.ofAlgHom (rootCoordSign n) (rootCoordSignInv n)
    (rootCoordSign_comp_signInv n) (rootCoordSignInv_comp_sign n)

theorem lowerRootMap_eq_signed_rootMap (n : ℕ) (r : Depth.RB n) :
    (show RootPolynomial n from lowerRootMap n r) = rootMap n (rootCoordEquiv n r) := by
  have h : ((rootPolynomialEquiv n).toAlgHom.comp (rootMap n)).comp
      (rootCoordSign n) = (lowerRootPolynomialEquiv n).toAlgHom.comp (lowerRootMap n) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, rootCoordSign, aeval_X, map_mul, map_pow, map_neg,
      map_one, rootMap_X, lowerRootMap_X]
    change (-1) ^ (n - (k : ℕ)) * esymm (Fin n) ℂ ((k.rev : ℕ) + 1) =
      (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin n) ℂ))).coeff k
    rw [Depth.coeff_prod_X_sub_C_X (Fin n) (by simp), Fintype.card_fin,
      Fin.val_rev, show n - ((k : ℕ) + 1) + 1 = n - k by omega]
  exact (AlgHom.congr_fun h r).symm

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- The identity on polynomials is semilinear for the signed coordinate change. -/
def lowerRootSemilinearEquiv (n : ℕ) :
    LowerRootPolynomial n ≃ₛₗ[((rootCoordEquiv n).toRingEquiv : Depth.RB n →+* Depth.RB n)] RootPolynomial n where
  toFun q := q
  invFun q := q
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r q := by
    change (show RootPolynomial n from lowerRootMap n r) * (show RootPolynomial n from q) =
      rootMap n (rootCoordEquiv n r) * (show RootPolynomial n from q)
    rw [lowerRootMap_eq_signed_rootMap]

/-- Freeness in lower coefficients transports to the elementary-coordinate action. -/
theorem rootPolynomial_free_of_lower (n : ℕ)
    [Module.Free (Depth.RB n) (LowerRootPolynomial n)] :
    Module.Free (Depth.RB n) (RootPolynomial n) :=
  Module.Free.of_equiv (lowerRootSemilinearEquiv n)

end KhanSL2.PolynomialBGG
