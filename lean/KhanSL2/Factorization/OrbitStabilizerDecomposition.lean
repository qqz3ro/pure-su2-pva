module

public import KhanSL2.Factorization.OrbitStabilizer

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.FiberTransport

variable {R G I : Type*} [CommRing R] [Group G] [MulAction G I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- Fixed vectors of the specified actual linear operators. -/
def fixedVectors (ρ : G → Module.End R V) : Submodule R V where
  carrier := {x | ∀ g, ρ g x = x}
  zero_mem' := by simp
  add_mem' hx hy g := by rw [map_add,hx g,hy g]
  smul_mem' c _ hx g := by rw [map_smul,hx g]

/-- An equivariant decomposition identifies actual fixed vectors with invariant
sections. The decomposition and its component formulas are retained explicitly. -/
def fixedVectorsEquivSections (T : FiberTransport (R:=R) (G:=G) M)
    (ρ : G → Module.End R V) (e : V ≃ₗ[R] ∀ i, M i)
    (he : ∀ (g : G) (i j : I) (h : g • i = j) (x : V),
      T.move g i j h (e x i) = e (ρ g x) j) :
    fixedVectors ρ ≃ₗ[R] T.invariantSections where
  toFun x := ⟨e x.val, fun g i j h => (he g i j h x.val).trans
    (congrArg (fun v => e v j) (x.property g))⟩
  invFun y := ⟨e.symm y.val, by
    intro g
    apply e.injective
    funext j
    have hij : g • (g⁻¹ • j) = j := smul_inv_smul g j
    rw [← he g (g⁻¹ • j) j hij,LinearEquiv.apply_symm_apply]
    exact y.property g (g⁻¹ • j) j hij⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val
  map_smul' c x := by apply Subtype.ext; exact e.map_smul c x.val

/-- The canonical orbit restriction from an equivariant product decomposition. -/
def fixedVectorsEquivStabilizer (T : FiberTransport (R:=R) (G:=G) M)
    (ρ : G → Module.End R V) (e : V ≃ₗ[R] ∀ i, M i)
    (he : ∀ (g : G) (i j : I) (h : g • i = j) (x : V),
      T.move g i j h (e x i) = e (ρ g x) j)
    (i₀ : I) (htrans : ∀ j : I, ∃ g : G, g • i₀ = j) :
    fixedVectors ρ ≃ₗ[R] T.stabilizerFixed i₀ :=
  (fixedVectorsEquivSections T ρ e he).trans (T.evaluationEquiv i₀ htrans)

@[simp] theorem fixedVectorsEquivStabilizer_apply (T : FiberTransport (R:=R) (G:=G) M)
    (ρ : G → Module.End R V) (e : V ≃ₗ[R] ∀ i, M i)
    (he : ∀ (g : G) (i j : I) (h : g • i = j) (x : V),
      T.move g i j h (e x i) = e (ρ g x) j)
    (i₀ : I) (htrans : ∀ j : I, ∃ g : G, g • i₀ = j) (x : fixedVectors ρ) :
    (fixedVectorsEquivStabilizer T ρ e he i₀ htrans x).val = e x.val i₀ := rfl

end KhanSL2.Factorization.FiberTransport
