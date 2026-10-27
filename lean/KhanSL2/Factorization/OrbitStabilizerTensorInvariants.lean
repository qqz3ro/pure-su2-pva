module

public import KhanSL2.Factorization.OrbitStabilizerAverage
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.FiberTransport

variable {R G H M N : Type*} [CommRing R] [Group G] [Fintype G] [Group H] [Fintype H]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The product-group representation on the actual tensor product. -/
def tensorAction (ρ : G →* Module.End R M) (τ : H →* Module.End R N) :
    G × H →* Module.End R (M ⊗[R] N) where
  toFun g := TensorProduct.map (ρ g.1) (τ g.2)
  map_one' := by simp only [Prod.fst_one,Prod.snd_one,map_one,TensorProduct.map_one]
  map_mul' g h := by
    simp only [Prod.fst_mul,Prod.snd_mul,map_mul,TensorProduct.map_mul]

/-- The ambient inclusion of the tensor product of fixed modules. -/
def tensorFixedInclusion (ρ : G →* Module.End R M) (τ : H →* Module.End R N) :
    (fixedVectors (fun g => ρ g) ⊗[R] fixedVectors (fun h => τ h)) →ₗ[R] M ⊗[R] N :=
  TensorProduct.map (fixedVectors (fun g => ρ g)).subtype (fixedVectors (fun h => τ h)).subtype

omit [Fintype G] [Fintype H] in
theorem tensorFixedInclusion_mem (ρ : G →* Module.End R M) (τ : H →* Module.End R N)
    (x : fixedVectors (fun g => ρ g) ⊗[R] fixedVectors (fun h => τ h)) :
    tensorFixedInclusion ρ τ x ∈ fixedVectors (fun g => tensorAction ρ τ g) := by
  intro g
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    change ρ g.1 m.val ⊗ₜ[R] τ g.2 n.val = m.val ⊗ₜ[R] n.val
    rw [m.property g.1,n.property g.2]
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Independent normalized projectors identify product-group invariants with
the actual tensor product of the two fixed modules. -/
def tensorFixedEquiv (ρ : G →* Module.End R M) (τ : H →* Module.End R N)
    (c d : R) (hc : c * (Fintype.card G : R) = 1) (hd : d * (Fintype.card H : R) = 1) :
    (fixedVectors (fun g => ρ g) ⊗[R] fixedVectors (fun h => τ h)) ≃ₗ[R]
      fixedVectors (fun g => tensorAction ρ τ g) := by
  let i := tensorFixedInclusion ρ τ
  let p := TensorProduct.map (averageProjection ρ c) (averageProjection τ d)
  have hleft : p.comp i = LinearMap.id := by
    dsimp [p,i,tensorFixedInclusion]
    rw [← TensorProduct.map_comp,averageProjection_leftInverse ρ c hc,
      averageProjection_leftInverse τ d hd,TensorProduct.map_id]
  have hproject : i.comp p = TensorProduct.map (average ρ c) (average τ d) := by
    dsimp [p,i,tensorFixedInclusion]
    rw [← TensorProduct.map_comp]
    rfl
  have havg : TensorProduct.map (average ρ c) (average τ d) =
      c • ∑ g : G, d • ∑ h : H, TensorProduct.map (ρ g) (τ h) := by
    change (TensorProduct.mapBilinear (RingHom.id R) M N M N (average ρ c) (average τ d)) = _
    simp only [average,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,
      TensorProduct.mapBilinear_apply]
    simp_rw [← Finset.smul_sum]
    rw [smul_comm d c,Finset.sum_comm]
  have hright (x : fixedVectors (fun g => tensorAction ρ τ g)) : i (p x.val) = x.val := by
    have hx (g : G) (h : H) : TensorProduct.map (ρ g) (τ h) x.val = x.val := x.property (g,h)
    change (i.comp p) x.val = x.val
    rw [hproject,havg]
    simp only [LinearMap.smul_apply,LinearMap.sum_apply,hx,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul R,smul_smul,hc,one_smul,
      ← Nat.cast_smul_eq_nsmul R,smul_smul,hd,one_smul]
  exact {
    toFun := fun x => ⟨i x,tensorFixedInclusion_mem ρ τ x⟩
    invFun := fun x => p x.val
    left_inv := fun x => LinearMap.congr_fun hleft x
    right_inv := fun x => Subtype.ext (hright x)
    map_add' := fun x y => Subtype.ext (i.map_add x y)
    map_smul' := fun a x => Subtype.ext (i.map_smul a x) }

@[simp] theorem tensorFixedEquiv_tmul (ρ : G →* Module.End R M) (τ : H →* Module.End R N)
    (c d : R) (hc : c * (Fintype.card G : R) = 1) (hd : d * (Fintype.card H : R) = 1)
    (x : fixedVectors (fun g => ρ g)) (y : fixedVectors (fun h => τ h)) :
    (tensorFixedEquiv ρ τ c d hc hd (x ⊗ₜ[R] y)).val = x.val ⊗ₜ[R] y.val := rfl

end KhanSL2.Factorization.FiberTransport


