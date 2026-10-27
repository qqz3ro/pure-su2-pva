module

public import KhanSL2.Factorization.NonnegativeConeQuasiIso
public import Mathlib.LinearAlgebra.TensorProduct.Prod

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TensorProduct
namespace KhanSL2.Factorization.NonnegativeCone

universe u v w
variable {R : Type u} [CommRing R]
variable (S : Type w) [CommRing S] [Algebra R S]

/-- Ordinary scalar extension of the actual chain groups and differentials. -/
def scalarComplex (C : ChainComplex (ModuleCat.{v} R) ℕ) : ChainComplex (ModuleCat.{max v w} S) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of S (S ⊗[R] C.X n))
    (fun n => ModuleCat.ofHom ((C.d (n+1) n).hom.baseChange S))
    (fun n => by
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp,ModuleCat.hom_ofHom,ModuleCat.hom_zero]
      rw [← LinearMap.baseChange_comp]
      have h := congrArg (fun q => q.hom.baseChange S) (C.d_comp_d (n+1+1) (n+1) n)
      simpa only [ModuleCat.hom_comp,ModuleCat.hom_zero,LinearMap.baseChange_zero] using h)

@[simp] theorem scalarComplex_X (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (scalarComplex S C).X n = ModuleCat.of S (S ⊗[R] C.X n) := rfl

@[simp] theorem scalarComplex_d (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (scalarComplex S C).d (n+1) n = ModuleCat.ofHom ((C.d (n+1) n).hom.baseChange S) := by
  simp only [scalarComplex,ChainComplex.of,ChainComplex.of_d]

variable {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D)

def scalarMap : scalarComplex S C ⟶ scalarComplex S D :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom ((φ.f n).hom.baseChange S)) (fun n => by
    rw [scalarComplex_d,scalarComplex_d]
    apply ModuleCat.hom_ext
    have h := congrArg (fun f => (ModuleCat.Hom.hom f).baseChange S) (φ.comm (n+1) n)
    simpa only [ModuleCat.hom_comp,ModuleCat.hom_ofHom,LinearMap.baseChange_comp] using h)

@[simp] theorem scalarMap_f (n : ℕ) :
    (scalarMap S φ).f n = ModuleCat.ofHom ((φ.f n).hom.baseChange S) := rfl

/-- Tensor product distributes over each cone group, preserving its two summands. -/
def scalarConeEquiv : ∀ n, (scalarComplex S (complex φ)).X n ≃ₗ[S]
    (complex (scalarMap S φ)).X n
  | 0 => LinearEquiv.refl S _
  | n+1 => TensorProduct.prodRight R S S (D.X (n+1)) (C.X n)

theorem scalarConeEquiv_d (n : ℕ) :
    ((complex (scalarMap S φ)).d (n+1) n).hom.comp (scalarConeEquiv S φ (n+1)).toLinearMap =
      (scalarConeEquiv S φ n).toLinearMap.comp ((scalarComplex S (complex φ)).d (n+1) n).hom := by
  rw [complex_d,scalarComplex_d,complex_d]
  simp only [ModuleCat.hom_ofHom]
  apply LinearMap.ext
  intro z
  change S ⊗[R] Term C D (n+1) at z
  induction z using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a z =>
    cases n with
    | zero =>
      rcases z with ⟨y,x⟩
      change differential (scalarMap S φ) 0
          (TensorProduct.prodRight R S S (D.X 1) (C.X 0) (a ⊗ₜ[R] (y,x))) =
        (differential φ 0).baseChange S (a ⊗ₜ[R] (y,x))
      rw [TensorProduct.prodRight_tmul,LinearMap.baseChange_tmul,differential_zero,differential_zero]
      change (D.d 1 0).hom.baseChange S (a ⊗ₜ[R] y) +
        (φ.f 0).hom.baseChange S (a ⊗ₜ[R] x) = a ⊗ₜ[R] (D.d 1 0 y + φ.f 0 x)
      rw [LinearMap.baseChange_tmul,LinearMap.baseChange_tmul,TensorProduct.tmul_add]
    | succ n =>
      rcases z with ⟨y,x⟩
      change differential (scalarMap S φ) (n+1)
          (TensorProduct.prodRight R S S (D.X (n+2)) (C.X (n+1)) (a ⊗ₜ[R] (y,x))) =
        TensorProduct.prodRight R S S (D.X (n+1)) (C.X n)
          ((differential φ (n+1)).baseChange S (a ⊗ₜ[R] (y,x)))
      rw [TensorProduct.prodRight_tmul,LinearMap.baseChange_tmul,differential_succ,
        differential_succ,TensorProduct.prodRight_tmul]
      simp only [show n+2 = (n+1)+1 from rfl,scalarComplex_d,scalarMap_f]
      change ((D.d (n+2) (n+1)).hom.baseChange S (a ⊗ₜ[R] y) +
        (φ.f (n+1)).hom.baseChange S (a ⊗ₜ[R] x),
        -(C.d (n+1) n).hom.baseChange S (a ⊗ₜ[R] x)) =
        (a ⊗ₜ[R] (D.d (n+2) (n+1) y + φ.f (n+1) x),a ⊗ₜ[R] (-C.d (n+1) n x))
      rw [LinearMap.baseChange_tmul,LinearMap.baseChange_tmul,LinearMap.baseChange_tmul,
        TensorProduct.tmul_add,TensorProduct.tmul_neg]
def scalarConeMap : scalarComplex S (complex φ) ⟶ complex (scalarMap S φ) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (scalarConeEquiv S φ n).toLinearMap)
    (fun n => ModuleCat.hom_ext (scalarConeEquiv_d S φ n))

/-- This is an isomorphism of complexes, not a claim that ordinary homology
commutes with a nonflat tensor product. -/
def scalarConeIso : scalarComplex S (complex φ) ≅ complex (scalarMap S φ) := by
  let : ∀ n, IsIso ((scalarConeMap S φ).f n) := fun n =>
    (scalarConeEquiv S φ n).toModuleIso.isIso_hom
  let : IsIso (scalarConeMap S φ) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (scalarConeMap S φ)

end KhanSL2.Factorization.NonnegativeCone
