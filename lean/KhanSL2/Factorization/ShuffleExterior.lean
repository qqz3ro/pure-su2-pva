module

public import KhanSL2.LieChains.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

@[expose] public section

/-! The canonical exterior shuffle coproduct, constructed from its square-zero
creation operators. The Koszul sign is carried by the exterior parity map. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorShuffle

variable (L : Type*) [AddCommGroup L] [Module ℂ L]

abbrev Ext := ExteriorAlgebra ℂ L
abbrev Tensor := Ext L ⊗[ℂ] Ext L

/-- Exterior parity, negating every generator. -/
def parity : Ext L →ₐ[ℂ] Ext L := ExteriorAlgebra.map (-LinearMap.id)

@[simp] theorem parity_ι (y : L) : parity L (ExteriorAlgebra.ι ℂ y) = -ExteriorAlgebra.ι ℂ y := by
  simp [parity]

@[simp] theorem parity_parity (u : Ext L) : parity L (parity L u) = u := by
  have h : (parity L).comp (parity L) = AlgHom.id ℂ (Ext L) := by
    ext y
    simp
  exact AlgHom.congr_fun h u

/-- The odd creation operator on an exterior tensor product. -/
def create (y : L) : Module.End ℂ (Tensor L) :=
  LinearMap.rTensor (Ext L) (LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ y)) +
    TensorProduct.map (parity L).toLinearMap (LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ y))

@[simp] theorem create_tmul (y : L) (u v : Ext L) :
    create L y (u ⊗ₜ[ℂ] v) =
      (ExteriorAlgebra.ι ℂ y * u) ⊗ₜ[ℂ] v +
        parity L u ⊗ₜ[ℂ] (ExteriorAlgebra.ι ℂ y * v) := rfl

/-- Creation is linear in the exterior generator. -/
def createLinear : L →ₗ[ℂ] Module.End ℂ (Tensor L) where
  toFun := create L
  map_add' y z := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.add_apply, create_tmul, map_add, add_mul,
      TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  map_smul' c y := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.smul_apply, create_tmul, map_smul, smul_mul_assoc,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add, RingHom.id_apply]

/-- Anticommutation of the two tensor-factor creations makes their sum square-zero. -/
theorem create_square (y : L) : create L y * create L y = 0 := by
  apply TensorProduct.ext'
  intro u v
  simp only [Module.End.mul_apply, create_tmul, map_add, map_mul, parity_ι,
    neg_mul, parity_parity, TensorProduct.neg_tmul, ← mul_assoc,
    ExteriorAlgebra.ι_sq_zero, zero_mul, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, LinearMap.zero_apply]
  abel

/-- The exterior algebra acts by the canonical signed tensor creation operators. -/
def representation : Ext L →ₐ[ℂ] Module.End ℂ (Tensor L) :=
  ExteriorAlgebra.lift ℂ ⟨createLinear L, create_square L⟩

@[simp] theorem representation_ι (y : L) :
    representation L (ExteriorAlgebra.ι ℂ y) = create L y :=
  ExteriorAlgebra.lift_ι_apply _ _ _ y

/-- The canonical shuffle coproduct, evaluated on the tensor unit. -/
def shuffle : Ext L →ₗ[ℂ] Tensor L where
  toFun u := representation L u ((1 : Ext L) ⊗ₜ[ℂ] (1 : Ext L))
  map_add' u v := by simp
  map_smul' c u := by simp

@[simp] theorem shuffle_one : shuffle L 1 = (1 : Ext L) ⊗ₜ[ℂ] (1 : Ext L) := by
  simp [shuffle]

/-- The defining shuffle recursion, with its actual Koszul parity. -/
theorem shuffle_ι_mul (y : L) (u : Ext L) :
    shuffle L (ExteriorAlgebra.ι ℂ y * u) = create L y (shuffle L u) := by
  simp only [shuffle, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
    representation_ι, Module.End.mul_apply]

@[simp] theorem shuffle_ι (y : L) :
    shuffle L (ExteriorAlgebra.ι ℂ y) =
      ExteriorAlgebra.ι ℂ y ⊗ₜ[ℂ] (1 : Ext L) +
        (1 : Ext L) ⊗ₜ[ℂ] ExteriorAlgebra.ι ℂ y := by
  simpa only [mul_one, shuffle_one, create_tmul, map_one] using
    shuffle_ι_mul L y (1 : Ext L)

/-- The exterior counit sends all positive exterior degrees to zero. -/
abbrev counit : Ext L →ₐ[ℂ] ℂ := ExteriorAlgebra.algebraMapInv

@[simp] theorem counit_ι (y : L) : counit L (ExteriorAlgebra.ι ℂ y) = 0 := by
  simp [counit, ExteriorAlgebra.algebraMapInv]

@[simp] theorem counit_parity (u : Ext L) : counit L (parity L u) = counit L u := by
  have h : (counit L).comp (parity L) = counit L := by
    ext y
    simp
  exact AlgHom.congr_fun h u

/-- Apply the counit to the left factor. -/
def counitLeft : Tensor L →ₗ[ℂ] Ext L :=
  (TensorProduct.lid ℂ (Ext L)).toLinearMap.comp
    (TensorProduct.map (counit L).toLinearMap LinearMap.id)

/-- Apply the counit to the right factor. -/
def counitRight : Tensor L →ₗ[ℂ] Ext L :=
  (TensorProduct.rid ℂ (Ext L)).toLinearMap.comp
    (TensorProduct.map LinearMap.id (counit L).toLinearMap)

@[simp] theorem counitLeft_tmul (u v : Ext L) :
    counitLeft L (u ⊗ₜ[ℂ] v) = counit L u • v := rfl

@[simp] theorem counitRight_tmul (u v : Ext L) :
    counitRight L (u ⊗ₜ[ℂ] v) = counit L v • u := rfl

theorem counitLeft_create (y : L) (z : Tensor L) :
    counitLeft L (create L y z) = ExteriorAlgebra.ι ℂ y * counitLeft L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [create_tmul, map_add, counitLeft_tmul, map_mul, counit_ι,
      zero_mul, zero_smul, zero_add, counit_parity, mul_smul_comm]
  | add z w hz hw => simp only [map_add, hz, hw, mul_add]

theorem counitRight_create (y : L) (z : Tensor L) :
    counitRight L (create L y z) = ExteriorAlgebra.ι ℂ y * counitRight L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [create_tmul, map_add, counitRight_tmul, map_mul, counit_ι,
      zero_mul, zero_smul, add_zero, mul_smul_comm]
  | add z w hz hw => simp only [map_add, hz, hw, mul_add]

/-- The actual shuffle coproduct is left counital. -/
@[simp] theorem counitLeft_shuffle (u : Ext L) : counitLeft L (shuffle L u) = u := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, shuffle_one]
    simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu => rw [shuffle_ι_mul, counitLeft_create, hu]

/-- The actual shuffle coproduct is right counital. -/
@[simp] theorem counitRight_shuffle (u : Ext L) : counitRight L (shuffle L u) = u := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, shuffle_one]
    simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu => rw [shuffle_ι_mul, counitRight_create, hu]

end KhanSL2.Factorization.ExteriorShuffle

