module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.GroupAction.Basic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization

variable {R G I : Type*} [CommRing R] [Group G] [MulAction G I]
variable (M : I → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Coherent linear transport between the actual fibres of a group action.
The explicit target equality keeps dependent quotient fibres visible. -/
structure FiberTransport where
  move : ∀ (g : G) (i j : I), g • i = j → M i ≃ₗ[R] M j
  one_apply : ∀ (i : I) (x : M i), move 1 i i (one_smul G i) x = x
  mul_apply : ∀ (g h : G) (i j k : I) (hh : h • i = j) (hg : g • j = k) (x : M i),
    move (g*h) i k (by rw [mul_smul,hh,hg]) x =
      move g j k hg (move h i j hh x)

namespace FiberTransport
variable {M} (T : FiberTransport (R:=R) (G:=G) M)

/-- Actual invariant sections of the transported family. -/
def invariantSections : Submodule R (∀ i, M i) where
  carrier := {x | ∀ (g : G) (i j : I) (h : g • i = j), T.move g i j h (x i) = x j}
  zero_mem' := by simp
  add_mem' hx hy g i j h := by rw [Pi.add_apply, Pi.add_apply, map_add, hx g i j h, hy g i j h]
  smul_mem' c _ hx g i j h := by rw [Pi.smul_apply, Pi.smul_apply, map_smul, hx g i j h]

/-- Actual fixed vectors for the stabilizer of the chosen assignment. -/
def stabilizerFixed (i₀ : I) : Submodule R (M i₀) where
  carrier := {x | ∀ (g : G) (h : g • i₀ = i₀), T.move g i₀ i₀ h x = x}
  zero_mem' := by simp
  add_mem' hx hy g h := by rw [map_add, hx g h, hy g h]
  smul_mem' c _ hx g h := by rw [map_smul, hx g h]

/-- Evaluation at an orbit representative, with its precise stabilizer condition. -/
def evaluation (i₀ : I) : T.invariantSections →ₗ[R] T.stabilizerFixed i₀ where
  toFun x := ⟨x.val i₀, fun g h => x.property g i₀ i₀ h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transport of a stabilizer-fixed vector does not depend on a transporter choice. -/
theorem move_eq_of_stabilizerFixed (i₀ j : I) (x : T.stabilizerFixed i₀)
    (g h : G) (hg : g • i₀ = j) (hh : h • i₀ = j) :
    T.move g i₀ j hg x.val = T.move h i₀ j hh x.val := by
  have hs : (h⁻¹*g) • i₀ = i₀ := by
    rw [mul_smul,hg,← hh,inv_smul_smul]
  have he := T.mul_apply h (h⁻¹*g) i₀ i₀ j hs hh x.val
  rw [x.property (h⁻¹*g) hs] at he
  simpa only [mul_inv_cancel_left] using he

variable (i₀ : I) (htrans : ∀ j : I, ∃ g : G, g • i₀ = j)

/-- Extend the stabilizer-fixed vector to its uniquely determined invariant section.
No averaging, division, or reducedness of the scalar ring is used. -/
def extend : T.stabilizerFixed i₀ →ₗ[R] T.invariantSections where
  toFun x := ⟨fun j => T.move (htrans j).choose i₀ j (htrans j).choose_spec x.val, by
    intro g i j h
    have hi := (htrans i).choose_spec
    have hj := (htrans j).choose_spec
    have hgi : (g*(htrans i).choose) • i₀ = j := by rw [mul_smul,hi,h]
    rw [← T.mul_apply g (htrans i).choose i₀ i j hi h]
    exact T.move_eq_of_stabilizerFixed i₀ j x (g*(htrans i).choose) (htrans j).choose hgi hj⟩
  map_add' x y := by
    apply Subtype.ext
    funext j
    exact map_add (T.move (htrans j).choose i₀ j (htrans j).choose_spec) x.val y.val
  map_smul' c x := by
    apply Subtype.ext
    funext j
    exact map_smul (T.move (htrans j).choose i₀ j (htrans j).choose_spec) c x.val

@[simp] theorem evaluation_extend (x : T.stabilizerFixed i₀) :
    T.evaluation i₀ (T.extend i₀ htrans x) = x := by
  apply Subtype.ext
  exact x.property (htrans i₀).choose (htrans i₀).choose_spec

@[simp] theorem extend_evaluation (x : T.invariantSections) :
    T.extend i₀ htrans (T.evaluation i₀ x) = x := by
  apply Subtype.ext
  funext j
  exact x.property (htrans j).choose i₀ j (htrans j).choose_spec

/-- Orbit/stabilizer descent for actual linear fibres: invariant sections are
precisely the stabilizer-fixed vectors in one fibre. Signed actions are included. -/
def evaluationEquiv : T.invariantSections ≃ₗ[R] T.stabilizerFixed i₀ where
  __ := T.evaluation i₀
  invFun := T.extend i₀ htrans
  left_inv := T.extend_evaluation i₀ htrans
  right_inv := T.evaluation_extend i₀ htrans

@[simp] theorem evaluationEquiv_apply (x : T.invariantSections) :
    (T.evaluationEquiv i₀ htrans x).val = x.val i₀ := rfl

end FiberTransport
end KhanSL2.Factorization

