module

public import KhanSL2.SymmetricFamily.BaseChangedAction
public import KhanSL2.SymmetricFamily.LocalRootTopLine

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Genuine one-point specializations of the original symmetric and exterior
current coefficient modules. Their root-coordinate maps are the original
normalized tensor sections after this exact coefficient specialization. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald

/-- The prescribed coefficient specialization at the divisor k[a]. -/
abbrev localCoefficientAlgebra (k : ℕ) (a : ℂ) : Algebra (Depth.RB k) ℂ :=
  (Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).toRingHom.toAlgebra

/-- A separate current-module interpretation of the actual coefficient fibre. -/
def LocalCoefficientFibre (k : ℕ) (M : Type*) [AddCommGroup M] [Module (Depth.RB k) M]
    (a : ℂ) : Type _ :=
  letI := localCoefficientAlgebra k a
  CoefficientBaseChange (Depth.RB k) M ℂ

variable (k : ℕ) (M : Type*) [AddCommGroup M] [Module (Depth.RB k) M] (a : ℂ)

instance : AddCommGroup (LocalCoefficientFibre k M a) := by
  unfold LocalCoefficientFibre
  infer_instance
instance : Module ℂ (LocalCoefficientFibre k M a) := by
  unfold LocalCoefficientFibre
  infer_instance

variable [Module ℂ M] [IsScalarTower ℂ (Depth.RB k) M]
  [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [CoefficientLinearCurrent (Depth.RB k) M]

instance : LieRingModule BGG.Current (LocalCoefficientFibre k M a) := by
  unfold LocalCoefficientFibre
  infer_instance
instance : LieModule ℂ BGG.Current (LocalCoefficientFibre k M a) := by
  unfold LocalCoefficientFibre
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  infer_instance

instance [Module.Finite (Depth.RB k) M] : FiniteDimensional ℂ (LocalCoefficientFibre k M a) := by
  unfold LocalCoefficientFibre
  infer_instance

/-- The genuine symmetric coefficient fibre at k[a]. -/
abbrev LocalSymmetricFibre (k : ℕ) (a : ℂ) := LocalCoefficientFibre k (symmetricPower k) a

/-- The genuine original exterior coefficient fibre at k[a]. -/
abbrev LocalExteriorFibre (k : ℕ) (a : ℂ) := LocalCoefficientFibre k (⋀[ℂ]^k BGG.Current) a

instance localSymmetricFibre_finite (k : ℕ) (a : ℂ) : FiniteDimensional ℂ (LocalSymmetricFibre k a) := by
  let := symmetricPower_finite k
  infer_instance

instance localExteriorFibre_finite (k : ℕ) (a : ℂ) : FiniteDimensional ℂ (LocalExteriorFibre k a) := by
  let := exteriorPower_finite k
  infer_instance

/-- The actual normalized symmetric coefficient inclusion into local root/color tensors. -/
def localSymmetricRootInclusion (k : ℕ) (a : ℂ) :
    LocalSymmetricFibre k a →ₗ[ℂ] LocalRootColors k a := by
  letI := localCoefficientAlgebra k a
  letI : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  exact symmetricCoefficientRootInclusion k ℂ

/-- The normalized map faithfully represents the actual local symmetric fibre. -/
theorem localSymmetricRootInclusion_injective (k : ℕ) (a : ℂ) :
    Function.Injective (localSymmetricRootInclusion k a) := by
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  intro x y h
  apply (symmetricBaseChangedLabelledEquiv k ℂ).injective
  exact Subtype.ext h

/-- The actual local symmetric fibre satisfies the honest simultaneous slot invariance. -/
theorem localSymmetricRootInclusion_invariant (k : ℕ) (a : ℂ)
    (x : LocalSymmetricFibre k a) (σ : Equiv.Perm (Fin k)) :
    localRootColorPermute k a σ (localSymmetricRootInclusion k a x) =
      localSymmetricRootInclusion k a x := by
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  exact (symmetricBaseChangedLabelledEquiv k ℂ x).property σ.symm

/-- The original specialized current action is the literal local root-slot action. -/
theorem localSymmetricRootInclusion_mode (k : ℕ) (a : ℂ) (n : ℕ) (x : BGG.G)
    (v : LocalSymmetricFibre k a) :
    localSymmetricRootInclusion k a ⁅BGG.mode n x,v⁆ =
      localRootColorMode k a n (LieAlgebra.ad ℂ BGG.G x)
        (localSymmetricRootInclusion k a v) := by
  let := localCoefficientAlgebra k a
  let : IsScalarTower ℂ (Depth.RB k) ℂ :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Collision.coeffHom k ((Polynomial.X - Polynomial.C a)^k)).commutes z).symm
  exact symmetricCoefficientRootInclusion_mode k ℂ n x v

end KhanSL2.SymmetricFamily
