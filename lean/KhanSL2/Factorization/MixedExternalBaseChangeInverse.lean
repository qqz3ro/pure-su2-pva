module

public import KhanSL2.Factorization.MixedExternalBaseChange

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Factorization.MixedExternal

/-- Extend a specified coefficient-linear map by its literal scalar multiplication formula. -/
def extendScalarsMap {K A V W : Type*} [CommRing K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module A W]
    [IsScalarTower K A W] (f : V →ₗ[K] W) : A ⊗[K] V →ₗ[A] W :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • f
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }

@[simp] theorem extendScalarsMap_tmul {K A V W : Type*} [CommRing K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module A W]
    [IsScalarTower K A W] (f : V →ₗ[K] W) (a : A) (v : V) :
    extendScalarsMap f (a ⊗ₜ[K] v) = a • f v := rfl

variable (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
  [Algebra ℂ R] [Algebra ℂ S]
  [Algebra R A] [Algebra S A] [Algebra (R ⊗[ℂ] S) A]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]

variable (h : ∀ r : R, ∀ s : S, algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] s) =
  algebraMap R A r * algebraMap S A s)

include h

/-- The literal elementary class in the jointly extended original module. -/
def sourceUnit (m : M) (n : N) : Source R S A M N :=
  (1:A) ⊗ₜ[R ⊗[ℂ] S] (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n)

/-- The elementary external class respects the original second-ring balancing relation. -/
theorem sourceUnit_right_smul (s : S) (m : M) (n : N) :
    sourceUnit R S A M N m (s • n) = s • sourceUnit R S A M N m n := by
  let U := TensorProduct.mk (R ⊗[ℂ] S) A (ExternalTensor R S M N) 1
  have he : (show ExternalTensor R S M N from m ⊗ₜ[ℂ] (s • n)) =
      ((1:R) ⊗ₜ[ℂ] s) • (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n) := by
    change (m ⊗ₜ[ℂ] (s • n) : M ⊗[ℂ] N) = ((1:R) • m) ⊗ₜ[ℂ] (s • n)
    rw [one_smul]
  calc
    sourceUnit R S A M N m (s • n) =
        U (((1:R) ⊗ₜ[ℂ] s) • (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n)) := congrArg U he
    _ = ((1:R) ⊗ₜ[ℂ] s) • sourceUnit R S A M N m n := U.map_smul _ _
    _ = algebraMap (R ⊗[ℂ] S) A ((1:R) ⊗ₜ[ℂ] s) • sourceUnit R S A M N m n :=
      (IsScalarTower.algebraMap_smul A _ _).symm
    _ = algebraMap S A s • sourceUnit R S A M N m n := by rw [h,map_one,one_mul]
    _ = s • sourceUnit R S A M N m n := IsScalarTower.algebraMap_smul A _ _

/-- The elementary external class respects the original first-ring balancing relation. -/
theorem sourceUnit_left_smul (r : R) (m : M) (n : N) :
    sourceUnit R S A M N (r • m) n = r • sourceUnit R S A M N m n := by
  let U := TensorProduct.mk (R ⊗[ℂ] S) A (ExternalTensor R S M N) 1
  have he : (show ExternalTensor R S M N from (r • m) ⊗ₜ[ℂ] n) =
      (r ⊗ₜ[ℂ] (1:S)) • (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n) := by
    change ((r • m) ⊗ₜ[ℂ] n : M ⊗[ℂ] N) = (r • m) ⊗ₜ[ℂ] ((1:S) • n)
    rw [one_smul]
  calc
    sourceUnit R S A M N (r • m) n =
        U ((r ⊗ₜ[ℂ] (1:S)) • (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n)) := congrArg U he
    _ = (r ⊗ₜ[ℂ] (1:S)) • sourceUnit R S A M N m n := U.map_smul _ _
    _ = algebraMap (R ⊗[ℂ] S) A (r ⊗ₜ[ℂ] (1:S)) • sourceUnit R S A M N m n :=
      (IsScalarTower.algebraMap_smul A _ _).symm
    _ = algebraMap R A r • sourceUnit R S A M N m n := by rw [h,map_one,mul_one]
    _ = r • sourceUnit R S A M N m n := IsScalarTower.algebraMap_smul A _ _

def inverseRightUnit (m : M) : N →ₗ[S] Source R S A M N where
  toFun n := sourceUnit R S A M N m n
  map_add' n n' := by simp only [sourceUnit,TensorProduct.tmul_add]
  map_smul' s n := sourceUnit_right_smul R S A M N h s m n

def inverseRight (m : M) : A ⊗[S] N →ₗ[A] Source R S A M N :=
  extendScalarsMap (inverseRightUnit R S A M N h m)

@[simp] theorem inverseRight_tmul (m : M) (b : A) (n : N) :
    inverseRight R S A M N h m (b ⊗ₜ[S] n) =
      b • (sourceUnit R S A M N m n) := rfl

def inverseLeftUnit : M →ₗ[R] (A ⊗[S] N →ₗ[A] Source R S A M N) where
  toFun := inverseRight R S A M N h
  map_add' m m' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b n
    simp only [inverseRight_tmul,LinearMap.add_apply,sourceUnit,TensorProduct.add_tmul,TensorProduct.tmul_add,smul_add]
  map_smul' r m := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b n
    change b • (sourceUnit R S A M N (r • m) n) =
      r • (b • (sourceUnit R S A M N m n))
    rw [sourceUnit_left_smul R S A M N h r m n,smul_comm]

/-- Combine the two prescribed factor extensions into the original external scalar extension. -/
def inverse : Target R S A M N →ₗ[A] Source R S A M N :=
  TensorProduct.lift (extendScalarsMap (K:=R) (A:=A) (V:=M)
    (W:=A ⊗[S] N →ₗ[A] Source R S A M N) (inverseLeftUnit R S A M N h))

@[simp] theorem inverse_tmul (a b : A) (m : M) (n : N) :
    inverse R S A M N h ((a ⊗ₜ[R] m) ⊗ₜ[A] (b ⊗ₜ[S] n)) =
      (a*b) ⊗ₜ[R ⊗[ℂ] S] (show ExternalTensor R S M N from m ⊗ₜ[ℂ] n) := by
  change a • (b • (sourceUnit R S A M N m n)) = _
  rw [← mul_smul,sourceUnit,TensorProduct.smul_tmul',smul_eq_mul,mul_one]

end KhanSL2.Factorization.MixedExternal
