module

public import KhanSL2.Factorization.RelativeChainsDecomposition
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
open KhanSL2.BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- The actual categorical tensor complex of the two relative CE complexes. -/
abbrev tensorComplex : ChainComplex (ModuleCat ℂ) ℕ :=
  HomologicalComplex.tensorObj (complex M) (complex N)

/-- Inclusion of one bidegree into the actual categorical degree-sum tensor. -/
abbrev tensorDegreeInclusion (p q n : ℕ) (h : p + q = n) :
    degree M p ⊗[ℂ] degree N q →ₗ[ℂ] (tensorComplex M N).X n :=
  (HomologicalComplex.ιTensorObj (complex M) (complex N) p q n h).hom

/-- Forget the homogeneous bidegree of the actual categorical tensor term. -/
def tensorDegreeForget (n : ℕ) :
    (tensorComplex M N).X n →ₗ[ℂ] RelativeChains M ⊗[ℂ] RelativeChains N :=
  (HomologicalComplex.mapBifunctorDesc (K₁ := complex M) (K₂ := complex N)
    (F := MonoidalCategory.curriedTensor (ModuleCat ℂ)) (c := ComplexShape.down ℕ)
    (j := n) (A := ModuleCat.of ℂ (RelativeChains M ⊗[ℂ] RelativeChains N))
    (fun p q _ => ModuleCat.ofHom
      (TensorProduct.map (degree M p).subtype (degree N q).subtype))).hom

/-- On each categorical summand the forgetful map is precisely the two subtype maps. -/
@[reassoc]
theorem tensorDegreeInclusion_forget (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj (complex M) (complex N) p q n h ≫
      ModuleCat.ofHom (tensorDegreeForget M N n) =
        ModuleCat.ofHom (TensorProduct.map (degree M p).subtype (degree N q).subtype) := by
  exact HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := complex M) (K₂ := complex N)
    (F := MonoidalCategory.curriedTensor (ModuleCat ℂ)) (c := ComplexShape.down ℕ)
    (j := n) (A := ModuleCat.of ℂ (RelativeChains M ⊗[ℂ] RelativeChains N))
    (fun p q _ => ModuleCat.ofHom
      (TensorProduct.map (degree M p).subtype (degree N q).subtype)) p q h

@[simp] theorem tensorDegreeForget_inclusion (p q n : ℕ) (h : p + q = n)
    (z : degree M p ⊗[ℂ] degree N q) :
    tensorDegreeForget M N n (tensorDegreeInclusion M N p q n h z) =
      TensorProduct.map (degree M p).subtype (degree N q).subtype z := by
  have hι := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := complex M) (K₂ := complex N)
    (F := MonoidalCategory.curriedTensor (ModuleCat ℂ)) (c := ComplexShape.down ℕ)
    (j := n) (A := ModuleCat.of ℂ (RelativeChains M ⊗[ℂ] RelativeChains N))
    (fun p q _ => ModuleCat.ofHom
      (TensorProduct.map (degree M p).subtype (degree N q).subtype)) p q h
  exact congrArg (fun f => (f : _ ⟶ ModuleCat.of ℂ
    (RelativeChains M ⊗[ℂ] RelativeChains N)).hom z) hι

/-- The canonical bidegree projection into a prescribed degree sum. -/
def tensorDegreeComponent (n : ℕ) :
    RelativeChains M ⊗[ℂ] RelativeChains N →ₗ[ℂ] (tensorComplex M N).X n :=
  ∑ p ∈ Finset.range (n + 1),
    if hp : p ≤ n then
      (tensorDegreeInclusion M N p (n-p) n (Nat.add_sub_of_le hp)).comp
        (TensorProduct.map (degreeComponent M p) (degreeComponent N (n-p)))
    else 0

@[simp] theorem tensorDegreeComponent_tmul (n : ℕ)
    (u : RelativeChains M) (v : RelativeChains N) :
    tensorDegreeComponent M N n (u ⊗ₜ[ℂ] v) =
      ∑ p ∈ Finset.range (n + 1),
        if hp : p ≤ n then
          tensorDegreeInclusion M N p (n-p) n (Nat.add_sub_of_le hp)
            (degreeComponent M p u ⊗ₜ[ℂ] degreeComponent N (n-p) v)
        else 0 := by
  simp only [tensorDegreeComponent, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp

/-- The component map recovers the prescribed inclusion on each homogeneous tensor. -/
theorem tensorDegreeComponent_subtype_tmul (p q n : ℕ) (h : p + q = n)
    (u : degree M p) (v : degree N q) :
    tensorDegreeComponent M N n (u.val ⊗ₜ[ℂ] v.val) =
      tensorDegreeInclusion M N p q n h (u ⊗ₜ[ℂ] v) := by
  have hp : p ≤ n := by omega
  have hq : q = n - p := by omega
  subst q
  rw [tensorDegreeComponent_tmul]
  rw [Finset.sum_eq_single p]
  · simp only [dif_pos hp, degreeComponent_subtype]
  · intro r hr hrp
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    simp only [dif_pos hrn, degreeComponent_subtype_ne M hrp,
      TensorProduct.zero_tmul, map_zero]
  · intro hpnot
    exact (hpnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hp))).elim

/-- The canonical degree-sum forgetful map is split injective. -/
theorem tensorDegreeComponent_forget (n : ℕ) (z : (tensorComplex M N).X n) :
    tensorDegreeComponent M N n (tensorDegreeForget M N n z) = z := by
  have heq : ModuleCat.ofHom ((tensorDegreeComponent M N n).comp
      (tensorDegreeForget M N n)) = 𝟙 ((tensorComplex M N).X n) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v

    change tensorDegreeComponent M N n (tensorDegreeForget M N n
      (tensorDegreeInclusion M N p q n h (u ⊗ₜ[ℂ] v))) =
        tensorDegreeInclusion M N p q n h (u ⊗ₜ[ℂ] v)
    rw [tensorDegreeForget_inclusion, TensorProduct.map_tmul]
    exact tensorDegreeComponent_subtype_tmul M N p q n h u v
  exact congrArg (fun f => f.hom z) heq

theorem tensorDegreeForget_injective (n : ℕ) :
    Function.Injective (tensorDegreeForget M N n) :=
  Function.LeftInverse.injective (tensorDegreeComponent_forget M N n)

end KhanSL2.Factorization
