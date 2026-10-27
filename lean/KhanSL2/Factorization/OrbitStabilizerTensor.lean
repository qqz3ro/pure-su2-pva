module

public import KhanSL2.Factorization.OrbitStabilizer
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.FiberTransport

variable {R G I : Type*} [CommRing R] [Group G] [MulAction G I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {W : Type*} [AddCommGroup W] [Module R W]

/-- Add the actual auxiliary color representation to every root-assignment fibre. -/
def tensor (T : FiberTransport (R:=R) (G:=G) M) (ρ : G →* (W ≃ₗ[R] W)) :
    FiberTransport (R:=R) (G:=G) (fun i => M i ⊗[R] W) where
  move g i j h := TensorProduct.congr (T.move g i j h) (ρ g)
  one_apply i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m w =>
      simp only [TensorProduct.congr_tmul,T.one_apply,map_one]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  mul_apply g h i j k hh hg x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m w =>
      simp only [TensorProduct.congr_tmul,map_mul]
      rw [T.mul_apply g h i j k hh hg]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

@[simp] theorem tensor_move_tmul (T : FiberTransport (R:=R) (G:=G) M)
    (ρ : G →* (W ≃ₗ[R] W)) (g : G) (i j : I) (h : g • i = j) (m : M i) (w : W) :
    (T.tensor ρ).move g i j h (m ⊗ₜ[R] w) = T.move g i j h m ⊗ₜ[R] ρ g w :=
  TensorProduct.congr_tmul _ _ _ _

section SmallerScalars
variable {K W₀ : Type*} [CommRing K] [Algebra K R]
  [∀ i, Module K (M i)] [∀ i, IsScalarTower K R (M i)]
  [AddCommGroup W₀] [Module K W₀]

/-- Heterobasic transport: quotient fibres are R-modules, while the auxiliary
color representation is only defined over K. The resulting action remains R-linear. -/
def tensorOver (T : FiberTransport (R:=R) (G:=G) M) (ρ : G →* (W₀ ≃ₗ[K] W₀)) :
    FiberTransport (R:=R) (G:=G) (fun i => M i ⊗[K] W₀) where
  move g i j h := TensorProduct.AlgebraTensorModule.congr (T.move g i j h) (ρ g)
  one_apply i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m w =>
      simp only [TensorProduct.AlgebraTensorModule.congr_tmul,T.one_apply,map_one]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  mul_apply g h i j k hh hg x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m w =>
      simp only [TensorProduct.AlgebraTensorModule.congr_tmul,map_mul]
      rw [T.mul_apply g h i j k hh hg]
      rfl
    | add x y hx hy => simp only [map_add,hx,hy]

@[simp] theorem tensorOver_move_tmul (T : FiberTransport (R:=R) (G:=G) M)
    (ρ : G →* (W₀ ≃ₗ[K] W₀)) (g : G) (i j : I) (h : g • i = j) (m : M i) (w : W₀) :
    (T.tensorOver ρ).move g i j h (m ⊗ₜ[K] w) = T.move g i j h m ⊗ₜ[K] ρ g w :=
  TensorProduct.AlgebraTensorModule.congr_tmul _ _ _ _

end SmallerScalars
end KhanSL2.Factorization.FiberTransport


