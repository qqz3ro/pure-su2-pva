module

public import KhanSL2.Factorization.OrbitStabilizerDecomposition

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.FiberTransport

variable {R G I H : Type*} [CommRing R] [Group G] [MulAction G I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- An explicit parametrization of a stabilizer and an equivariant fibre
identification give an identification with the prescribed fixed operators. -/
def stabilizerFixedCongr (T : FiberTransport (R:=R) (G:=G) M) (i : I)
    (f : H → G) (hf : ∀ h, f h • i = i)
    (hsurj : ∀ g : G, g • i = i → ∃ h : H, f h = g)
    (ρ : H → Module.End R V) (e : M i ≃ₗ[R] V)
    (he : ∀ h : H, ∀ x : M i, e (T.move (f h) i i (hf h) x) = ρ h (e x)) :
    T.stabilizerFixed i ≃ₗ[R] fixedVectors ρ where
  toFun x := ⟨e x.val,by
    intro h
    rw [← he,x.property]⟩
  invFun y := ⟨e.symm y.val,by
    intro g hg
    obtain ⟨h,rfl⟩ := hsurj g hg
    apply e.injective
    rw [he,LinearEquiv.apply_symm_apply,y.property]⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c x.val

@[simp] theorem stabilizerFixedCongr_apply (T : FiberTransport (R:=R) (G:=G) M) (i : I)
    (f : H → G) (hf : ∀ h, f h • i = i)
    (hsurj : ∀ g : G, g • i = i → ∃ h : H, f h = g)
    (ρ : H → Module.End R V) (e : M i ≃ₗ[R] V)
    (he : ∀ h : H, ∀ x : M i, e (T.move (f h) i i (hf h) x) = ρ h (e x))
    (x : T.stabilizerFixed i) :
    (stabilizerFixedCongr T i f hf hsurj ρ e he x).val = e x.val := rfl

end KhanSL2.Factorization.FiberTransport
