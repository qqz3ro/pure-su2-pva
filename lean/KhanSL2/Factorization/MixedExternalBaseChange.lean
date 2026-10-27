module

public import KhanSL2.Factorization.ExternalTensor
public import KhanSL2.SymmetricFamily.FactorInsertion

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Factorization.MixedExternal

variable (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ A]
  [Algebra R A] [Algebra S A] [Algebra (R ⊗[ℂ] S) A]
  [IsScalarTower ℂ R A] [IsScalarTower ℂ S A]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]

abbrev Source := A ⊗[R ⊗[ℂ] S] ExternalTensor R S M N
abbrev Target := (A ⊗[R] M) ⊗[A] (A ⊗[S] N)

/-- Canonical unit insertion of both original modules into their separate scalar extensions. -/
def unit : ExternalTensor R S M N →ₗ[ℂ] Target R S A M N :=
  SymmetricFamily.tensorOverMap
    ((TensorProduct.mk R A M 1).restrictScalars ℂ)
    ((TensorProduct.mk S A N 1).restrictScalars ℂ)

omit [Algebra (R ⊗[ℂ] S) A] in
@[simp] theorem unit_tmul (m : M) (n : N) :
    unit R S A M N (m ⊗ₜ[ℂ] n) = ((1:A) ⊗ₜ[R] m) ⊗ₜ[A] ((1:A) ⊗ₜ[S] n) := rfl

/- The joint chart scalar map retains the specified two independent coefficient maps. -/
variable (h : ∀ r : R, ∀ s : S, algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) =
  algebraMap R A r * algebraMap S A s)

include h

theorem unit_smul (c : R ⊗[ℂ] S) (z : ExternalTensor R S M N) :
    unit R S A M N (c • z) = c • unit R S A M N z := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [add_smul,map_add,hc,hd]
  | tmul r s =>
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [smul_add,map_add,hz,hw]
    | tmul m n =>
      rw [← IsScalarTower.algebraMap_smul A (r ⊗ₜ[ℂ] s)
        (unit R S A M N (m ⊗ₜ[ℂ] n))]
      change ((1:A) ⊗ₜ[R] (r • m)) ⊗ₜ[A] ((1:A) ⊗ₜ[S] (s • n)) =
        algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) • (((1:A) ⊗ₜ[R] m) ⊗ₜ[A] ((1:A) ⊗ₜ[S] n))
      have hr : ((1:A) ⊗ₜ[R] (r • m) : A ⊗[R] M) =
          algebraMap R A r • ((1:A) ⊗ₜ[R] m) := by
        rw [IsScalarTower.algebraMap_smul A r]
        exact (TensorProduct.mk R A M 1).map_smul r m
      have hs : ((1:A) ⊗ₜ[S] (s • n) : A ⊗[S] N) =
          algebraMap S A s • ((1:A) ⊗ₜ[S] n) := by
        rw [IsScalarTower.algebraMap_smul A s]
        exact (TensorProduct.mk S A N 1).map_smul s n
      rw [hr,hs,h,TensorProduct.smul_tmul_smul]

/-- The same literal unit map respects the product coefficient ring. -/
def productUnit : ExternalTensor R S M N →ₗ[R ⊗[ℂ] S] Target R S A M N where
  toFun := unit R S A M N
  map_add' := (unit R S A M N).map_add
  map_smul' := unit_smul R S A M N h

/-- Original separate scalar extension on an elementary external tensor. -/
def forward : Source R S A M N →ₗ[A] Target R S A M N :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • productUnit R S A M N h
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }

@[simp] theorem forward_tmul (a : A) (m : M) (n : N) :
    forward R S A M N h (a ⊗ₜ[R ⊗[ℂ] S] (m ⊗ₜ[ℂ] n)) =
      (a ⊗ₜ[R] m) ⊗ₜ[A] ((1:A) ⊗ₜ[S] n) := by
  change a • (((1:A) ⊗ₜ[R] m) ⊗ₜ[A] ((1:A) ⊗ₜ[S] n)) = _
  simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]

end KhanSL2.Factorization.MixedExternal
