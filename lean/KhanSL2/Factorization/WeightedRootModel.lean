module

public import KhanSL2.SymmetricFamily.RootCharacteristic
public import KhanSL2.Factorization.WeightedRootsAlgebra

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace KhanSL2.Factorization.WeightedRootModel
open PolynomialBGG

/-- One labelled variable for each odd generator and for each even generator. -/
def LabelledWeightedRing (q r : ℕ) : Type := MvPolynomial (Fin q ⊕ Fin r) ℂ
instance (q r : ℕ) : CommRing (LabelledWeightedRing q r) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin q ⊕ Fin r) ℂ))
instance (q r : ℕ) : Nontrivial (LabelledWeightedRing q r) :=
  inferInstanceAs (Nontrivial (MvPolynomial (Fin q ⊕ Fin r) ℂ))
instance (q r : ℕ) : Algebra ℂ (LabelledWeightedRing q r) :=
  inferInstanceAs (Algebra ℂ (MvPolynomial (Fin q ⊕ Fin r) ℂ))

abbrev RootSlots (q r : ℕ) := Fin q ⊕ (Fin 2 × Fin r)

def rootIndexEquiv (q r : ℕ) : RootSlots q r ≃ Fin (q+2*r) :=
  (Equiv.sumCongr (Equiv.refl (Fin q)) finProdFinEquiv).trans finSumFinEquiv

def rootProjection (q r : ℕ) : RootSlots q r → Fin q ⊕ Fin r
  | .inl i => .inl i
  | .inr (_,j) => .inr j

def weightedRootIndex (q r : ℕ) : Fin (q+2*r) → Fin q ⊕ Fin r :=
  rootProjection q r ∘ (rootIndexEquiv q r).symm

@[simp] theorem weightedRootIndex_rootIndexEquiv (q r : ℕ) (i : RootSlots q r) :
    weightedRootIndex q r (rootIndexEquiv q r i) = rootProjection q r i := by
  simp [weightedRootIndex]

/-- Duplicate precisely the even roots, with multiplicity two. -/
def rootSubstitution (q r : ℕ) : RootPolynomial (q+2*r) →ₐ[ℂ] LabelledWeightedRing q r :=
  MvPolynomial.rename (weightedRootIndex q r)

/-- The original elementary coefficient variables act by the weighted roots. -/
def weightedRootMap (q r : ℕ) : Depth.RB (q+2*r) →ₐ[ℂ] LabelledWeightedRing q r :=
  (rootSubstitution q r).comp (rootMap (q+2*r))

instance (q r : ℕ) : Algebra (Depth.RB (q+2*r)) (LabelledWeightedRing q r) :=
  (weightedRootMap q r).toAlgebra
instance (q r : ℕ) : IsScalarTower ℂ (Depth.RB (q+2*r)) (LabelledWeightedRing q r) :=
  IsScalarTower.of_algebraMap_eq fun c => ((weightedRootMap q r).commutes c).symm

@[simp] theorem weightedRoot_algebraMap (q r : ℕ) (a : Depth.RB (q+2*r)) :
    algebraMap (Depth.RB (q+2*r)) (LabelledWeightedRing q r) a = weightedRootMap q r a := rfl

/-- The characteristic polynomial has odd-root multiplicity one and even-root multiplicity two. -/
def weightedCharacteristic (q r : ℕ) : Polynomial (LabelledWeightedRing q r) :=
  (∏ i : Fin q, (Polynomial.X - Polynomial.C (show LabelledWeightedRing q r from MvPolynomial.X (.inl i)))) *
    ∏ j : Fin r, (Polynomial.X - Polynomial.C (show LabelledWeightedRing q r from MvPolynomial.X (.inr j)))^2

theorem labelledCharacteristic_map (q r : ℕ) :
    (SymmetricFamily.labelledCharacteristic (q+2*r)).map (rootSubstitution q r).toRingHom =
      weightedCharacteristic q r := by
  have hx (i : Fin (q+2*r)) : (rootSubstitution q r).toRingHom
      (show RootPolynomial (q+2*r) from MvPolynomial.X i) =
      (show LabelledWeightedRing q r from MvPolynomial.X (weightedRootIndex q r i)) :=
    MvPolynomial.rename_X (weightedRootIndex q r) i
  simp only [SymmetricFamily.labelledCharacteristic,Polynomial.map_prod,
    Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,hx]
  change (∏ i : Fin (q+2*r), (Polynomial.X - Polynomial.C
    (show LabelledWeightedRing q r from MvPolynomial.X (weightedRootIndex q r i)))) = _
  rw [← (rootIndexEquiv q r).prod_comp]
  simp only [weightedRootIndex_rootIndexEquiv,Fintype.prod_sum_type,
    Fintype.prod_prod_type,rootProjection,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← Finset.prod_pow]
  rfl

theorem weightedCharacteristic_monic (q r : ℕ) : (weightedCharacteristic q r).Monic := by
  rw [← labelledCharacteristic_map]
  exact (SymmetricFamily.labelledCharacteristic_monic (q+2*r)).map _

@[simp] theorem weightedCharacteristic_natDegree (q r : ℕ) :
    (weightedCharacteristic q r).natDegree = q+2*r := by
  rw [← labelledCharacteristic_map,
    (SymmetricFamily.labelledCharacteristic_monic (q+2*r)).natDegree_map,
    SymmetricFamily.labelledCharacteristic_natDegree]

/-- The weighted map sends the universal polynomial to the actual characteristic polynomial. -/
theorem univPoly_map_weightedRootMap (q r : ℕ) :
    (Collision.univPoly (q+2*r)).map (weightedRootMap q r).toRingHom =
      weightedCharacteristic q r := by
  change (Collision.univPoly (q+2*r)).map
    ((rootSubstitution q r).toRingHom.comp (rootMap (q+2*r)).toRingHom) = _
  rw [← Polynomial.map_map,SymmetricFamily.univPoly_map_rootMap,labelledCharacteristic_map]

/-- Equality with the prescribed signed coefficient map, not an alternative scalar action. -/
theorem weightedRootMap_eq_coeffHom (q r : ℕ) :
    weightedRootMap q r = Collision.coeffHom (q+2*r) (weightedCharacteristic q r) := by
  rw [← labelledCharacteristic_map]
  apply MvPolynomial.algHom_ext
  intro i
  change rootSubstitution q r (rootMap (q+2*r) (MvPolynomial.X i)) = _
  rw [← SymmetricFamily.coeffHom_labelledCharacteristic]
  simp only [Collision.coeffHom,MvPolynomial.aeval_X,Collision.elemCoord,
    Polynomial.coeff_map,map_mul,map_pow,map_neg,map_one]
  rfl

@[simp] theorem weightedRootMap_X (q r : ℕ) (i : Fin (q+2*r)) :
    weightedRootMap q r (MvPolynomial.X i) =
      (-1 : LabelledWeightedRing q r)^(i.val+1) *
        (weightedCharacteristic q r).coeff (q+2*r-1-i.val) := by
  rw [weightedRootMap_eq_coeffHom]
  exact MvPolynomial.aeval_X _ _

/-- The exact weighted power sum, including the constant power sum m=0. -/
def weightedPowerSum (q r m : ℕ) : LabelledWeightedRing q r :=
  MvPolynomial.rename Sum.inl (MvPolynomial.psum (Fin q) ℂ m) +
    (2 : MvPolynomial (Fin q ⊕ Fin r) ℂ) *
      MvPolynomial.rename Sum.inr (MvPolynomial.psum (Fin r) ℂ m)

theorem rootSubstitution_powerSum (q r m : ℕ) :
    rootSubstitution q r (show RootPolynomial (q+2*r) from MvPolynomial.psum (Fin (q+2*r)) ℂ m) =
      weightedPowerSum q r m := by
  change MvPolynomial.rename (weightedRootIndex q r)
    (MvPolynomial.psum (Fin (q+2*r)) ℂ m) = _
  simp only [MvPolynomial.psum,map_sum,map_pow,MvPolynomial.rename_X]
  rw [← (rootIndexEquiv q r).sum_comp
    (fun i => (MvPolynomial.X (weightedRootIndex q r i) : MvPolynomial (Fin q ⊕ Fin r) ℂ)^m)]
  simp only [weightedRootIndex_rootIndexEquiv,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rootProjection,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  simp only [weightedPowerSum,MvPolynomial.psum,map_sum,map_pow,MvPolynomial.rename_X]

theorem weightedRootMap_powerSum (q r m : ℕ) :
    weightedRootMap q r ((Modules.elementaryAlgEquiv (q+2*r)).symm
      (Modules.powerSum (q+2*r) m)) = weightedPowerSum q r m := by
  change rootSubstitution q r (rootMap (q+2*r)
    ((Modules.elementaryAlgEquiv (q+2*r)).symm (Modules.powerSum (q+2*r) m))) = _
  rw [rootMap_apply,AlgEquiv.apply_symm_apply]
  exact rootSubstitution_powerSum q r m

end KhanSL2.Factorization.WeightedRootModel




