module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

/-! A finite normalized invariant projector commutes with arbitrary scalar
extension. No flatness or reducedness assumption is needed. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ι : Type*} [Fintype ι]

/-- Simultaneous fixed vectors of a specified family of linear operators. -/
def fixedOperators (ρ : ι → Module.End R M) : Submodule R M where
  carrier := {x | ∀ t, ρ t x = x}
  zero_mem' := by simp
  add_mem' hx hy t := by rw [map_add, hx t, hy t]
  smul_mem' c _ hx t := by rw [map_smul, hx t]

variable (S : Type*) [CommRing S] [Algebra R S]

/-- The normalized average formula survives arbitrary base change. -/
theorem splitAverage_baseChange (i : N →ₗ[R] M) (p : M →ₗ[R] N)
    (ρ : ι → Module.End R M) (c : R)
    (h : i.comp p = c • ∑ t, ρ t) :
    (i.baseChange S).comp (p.baseChange S) = c • ∑ t, (ρ t).baseChange S := by
  have hh := congrArg (fun f : Module.End R M => f.baseChange S) h
  rw [LinearMap.baseChange_comp] at hh
  change _ = (LinearMap.baseChangeHom R S M M) (c • ∑ t, ρ t) at hh
  simpa only [map_smul, map_sum, LinearMap.baseChangeHom_apply] using hh

/-- A split invariant projector gives exactly the invariant module after every base change. -/
def splitAverageBaseChangeEquiv (i : N →ₗ[R] M) (p : M →ₗ[R] N)
    (ρ : ι → Module.End R M) (c : R)
    (hc : c * (Fintype.card ι : R) = 1)
    (hpi : p.comp i = LinearMap.id)
    (hip : i.comp p = c • ∑ t, ρ t)
    (hi : ∀ t, (ρ t).comp i = i) :
    S ⊗[R] N ≃ₗ[S] fixedOperators (fun t => (ρ t).baseChange S) := by
  have hfix (x : S ⊗[R] N) : i.baseChange S x ∈
      fixedOperators (fun t => (ρ t).baseChange S) := by
    intro t
    have h := congrArg (fun f : N →ₗ[R] M => f.baseChange S) (hi t)
    rw [LinearMap.baseChange_comp] at h
    exact LinearMap.congr_fun h x
  have hleft (x : S ⊗[R] N) : p.baseChange S (i.baseChange S x) = x := by
    have h := congrArg (fun f : Module.End R N => f.baseChange S) hpi
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
    exact LinearMap.congr_fun h x
  have hright (x : S ⊗[R] M)
      (hx : x ∈ fixedOperators (fun t => (ρ t).baseChange S)) :
      i.baseChange S (p.baseChange S x) = x := by
    have h := LinearMap.congr_fun (splitAverage_baseChange S i p ρ c hip) x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply] at h
    change ∀ t, (ρ t).baseChange S x = x at hx
    rw [show (∑ t, (ρ t).baseChange S x) = (Fintype.card ι) • x by
      simp only [hx, Finset.sum_const, Finset.card_univ]] at h
    rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hc, one_smul] at h
    exact h
  exact {
    toFun := fun x => ⟨i.baseChange S x,hfix x⟩
    invFun := fun x => p.baseChange S x.val
    left_inv := hleft
    right_inv := fun x => Subtype.ext (hright x.val x.property)
    map_add' := fun x y => Subtype.ext ((i.baseChange S).map_add x y)
    map_smul' := fun a x => Subtype.ext ((i.baseChange S).map_smul a x) }

@[simp] theorem splitAverageBaseChangeEquiv_apply (i : N →ₗ[R] M) (p : M →ₗ[R] N)
    (ρ : ι → Module.End R M) (c : R)
    (hc : c * (Fintype.card ι : R) = 1)
    (hpi : p.comp i = LinearMap.id)
    (hip : i.comp p = c • ∑ t, ρ t)
    (hi : ∀ t, (ρ t).comp i = i) (x : S ⊗[R] N) :
    (splitAverageBaseChangeEquiv S i p ρ c hc hpi hip hi x).val = i.baseChange S x := rfl

end KhanSL2.SymmetricFamily
