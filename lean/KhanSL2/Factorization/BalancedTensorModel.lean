module

public import KhanSL2.Factorization.RelativeChainsScalarDegrees
public import KhanSL2.Factorization.BalancedShuffleDifferential
public import KhanSL2.Factorization.KunnethField

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The categorical degree-sum tensor has its canonical inclusion into the tensor
of the actual relative chain spaces. Its component maps use the specified quotient
projections, so this construction retains the chain and coefficient coordinates. -/

noncomputable section
open scoped TensorProduct BigOperators
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- The actual categorical tensor complex of the two relative CE complexes. -/
abbrev balancedTensorComplex : ChainComplex (ModuleCat A) ℕ :=
  HomologicalComplex.tensorObj (coefficientRelativeComplex A M) (coefficientRelativeComplex A N)

/-- Inclusion of one bidegree into the actual categorical degree-sum tensor. -/
abbrev balancedTensorDegreeInclusion (p q n : ℕ) (h : p + q = n) :
    degree M p ⊗[A] degree N q →ₗ[A] (balancedTensorComplex A M N).X n :=
  (HomologicalComplex.ιTensorObj (coefficientRelativeComplex A M) (coefficientRelativeComplex A N) p q n h).hom

/-- Forget the homogeneous bidegree of the actual categorical tensor term. -/
def balancedTensorDegreeForget (n : ℕ) :
    (balancedTensorComplex A M N).X n →ₗ[A] RelativeChains M ⊗[A] RelativeChains N :=
  (HomologicalComplex.mapBifunctorDesc (K₁ := coefficientRelativeComplex A M) (K₂ := coefficientRelativeComplex A N)
    (F := MonoidalCategory.curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
    (j := n) (A := ModuleCat.of A (RelativeChains M ⊗[A] RelativeChains N))
    (fun p q _ => ModuleCat.ofHom
      (TensorProduct.map (coefficientDegreeInclusionLinear A M p) (coefficientDegreeInclusionLinear A N q)))).hom

/-- On each categorical summand the forgetful map is precisely the two subtype maps. -/
@[reassoc]
theorem balancedTensorDegreeInclusion_forget (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj (coefficientRelativeComplex A M) (coefficientRelativeComplex A N) p q n h ≫
      ModuleCat.ofHom (balancedTensorDegreeForget A M N n) =
        ModuleCat.ofHom (TensorProduct.map (coefficientDegreeInclusionLinear A M p) (coefficientDegreeInclusionLinear A N q)) := by
  exact HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := coefficientRelativeComplex A M) (K₂ := coefficientRelativeComplex A N)
    (F := MonoidalCategory.curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
    (j := n) (A := ModuleCat.of A (RelativeChains M ⊗[A] RelativeChains N))
    (fun p q _ => ModuleCat.ofHom
      (TensorProduct.map (coefficientDegreeInclusionLinear A M p) (coefficientDegreeInclusionLinear A N q))) p q h

@[simp] theorem balancedTensorDegreeForget_inclusion (p q n : ℕ) (h : p + q = n)
    (z : degree M p ⊗[A] degree N q) :
    balancedTensorDegreeForget A M N n (balancedTensorDegreeInclusion A M N p q n h z) =
      TensorProduct.map (coefficientDegreeInclusionLinear A M p) (coefficientDegreeInclusionLinear A N q) z := by
  have hι := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := coefficientRelativeComplex A M) (K₂ := coefficientRelativeComplex A N)
    (F := MonoidalCategory.curriedTensor (ModuleCat A)) (c := ComplexShape.down ℕ)
    (j := n) (A := ModuleCat.of A (RelativeChains M ⊗[A] RelativeChains N))
    (fun p q _ => ModuleCat.ofHom
      (TensorProduct.map (coefficientDegreeInclusionLinear A M p) (coefficientDegreeInclusionLinear A N q))) p q h
  exact congrArg (fun f => (f : _ ⟶ ModuleCat.of A
    (RelativeChains M ⊗[A] RelativeChains N)).hom z) hι

/-- The canonical bidegree projection into a prescribed degree sum. -/
def balancedTensorDegreeComponent (n : ℕ) :
    RelativeChains M ⊗[A] RelativeChains N →ₗ[A] (balancedTensorComplex A M N).X n :=
  ∑ p ∈ Finset.range (n + 1),
    if hp : p ≤ n then
      (balancedTensorDegreeInclusion A M N p (n-p) n (Nat.add_sub_of_le hp)).comp
        (TensorProduct.map (coefficientDegreeComponentLinear A M p) (coefficientDegreeComponentLinear A N (n-p)))
    else 0

@[simp] theorem balancedTensorDegreeComponent_tmul (n : ℕ)
    (u : RelativeChains M) (v : RelativeChains N) :
    balancedTensorDegreeComponent A M N n (u ⊗ₜ[A] v) =
      ∑ p ∈ Finset.range (n + 1),
        if hp : p ≤ n then
          balancedTensorDegreeInclusion A M N p (n-p) n (Nat.add_sub_of_le hp)
            (coefficientDegreeComponentLinear A M p u ⊗ₜ[A] coefficientDegreeComponentLinear A N (n-p) v)
        else 0 := by
  simp only [balancedTensorDegreeComponent, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- The component map recovers the prescribed inclusion on each homogeneous tensor. -/
theorem balancedTensorDegreeComponent_subtype_tmul (p q n : ℕ) (h : p + q = n)
    (u : degree M p) (v : degree N q) :
    balancedTensorDegreeComponent A M N n (u.val ⊗ₜ[A] v.val) =
      balancedTensorDegreeInclusion A M N p q n h (u ⊗ₜ[A] v) := by
  have hp : p ≤ n := by omega
  have hq : q = n - p := by omega
  subst q
  rw [balancedTensorDegreeComponent_tmul]
  rw [Finset.sum_eq_single p]
  · simp only [dif_pos hp]
    change balancedTensorDegreeInclusion A M N p (n-p) n _
      (degreeComponent M p u.val ⊗ₜ[A] degreeComponent N (n-p) v.val) = _
    rw [degreeComponent_subtype,degreeComponent_subtype]
  · intro r hr hrp
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    simp only [dif_pos hrn]
    change balancedTensorDegreeInclusion A M N r (n-r) n _
      (degreeComponent M r u.val ⊗ₜ[A] degreeComponent N (n-r) v.val) = 0
    rw [degreeComponent_subtype_ne M hrp,TensorProduct.zero_tmul,map_zero]
  · intro hpnot
    exact (hpnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))).elim

/-- The canonical degree-sum forgetful map is split injective. -/
theorem balancedTensorDegreeComponent_forget (n : ℕ) (z : (balancedTensorComplex A M N).X n) :
    balancedTensorDegreeComponent A M N n (balancedTensorDegreeForget A M N n z) = z := by
  have heq : ModuleCat.ofHom ((balancedTensorDegreeComponent A M N n).comp
      (balancedTensorDegreeForget A M N n)) = 𝟙 ((balancedTensorComplex A M N).X n) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v

    change balancedTensorDegreeComponent A M N n (balancedTensorDegreeForget A M N n
      (balancedTensorDegreeInclusion A M N p q n h (u ⊗ₜ[A] v))) =
        balancedTensorDegreeInclusion A M N p q n h (u ⊗ₜ[A] v)
    rw [balancedTensorDegreeForget_inclusion, TensorProduct.map_tmul]
    exact balancedTensorDegreeComponent_subtype_tmul A M N p q n h u v
  exact congrArg (fun f => f.hom z) heq

theorem balancedTensorDegreeForget_injective (n : ℕ) :
    Function.Injective (balancedTensorDegreeForget A M N n) :=
  Function.LeftInverse.injective (balancedTensorDegreeComponent_forget A M N n)

end KhanSL2.Factorization



