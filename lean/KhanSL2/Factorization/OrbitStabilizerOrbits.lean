module

public import KhanSL2.Factorization.OrbitStabilizer

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.FiberTransport

variable {R G I J : Type*} [CommRing R] [Group G] [MulAction G I]
variable {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable (T : FiberTransport (R:=R) (G:=G) M) (rep : J → I)
  (hsep : ∀ (a b : J) (g : G), g • rep a = rep b → a = b)
  (hcover : ∀ i : I, ∃ (a : J) (g : G), g • rep a = i)

include hsep in
/-- Transport from any orbit representative is independent of its presentation. -/
theorem representative_move_eq (x : ∀ a : J, T.stabilizerFixed (rep a))
    (a b : J) (g h : G) (i : I) (hg : g • rep a = i) (hh : h • rep b = i) :
    T.move g (rep a) i hg (x a).val = T.move h (rep b) i hh (x b).val := by
  have hab : a = b := hsep a b (h⁻¹*g) (by rw [mul_smul,hg,← hh,inv_smul_smul])
  subst b
  exact T.move_eq_of_stabilizerFixed (rep a) i (x a) g h hg hh

/-- Simultaneous restriction to one representative of each orbit. -/
def orbitEvaluation : T.invariantSections →ₗ[R] ∀ a : J, T.stabilizerFixed (rep a) where
  toFun x a := T.evaluation (rep a) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Reconstruct an invariant section from its stabilizer-fixed orbit values. -/
def orbitExtend : (∀ a : J, T.stabilizerFixed (rep a)) →ₗ[R] T.invariantSections where
  toFun x := ⟨fun i => T.move (hcover i).choose_spec.choose (rep (hcover i).choose) i
    (hcover i).choose_spec.choose_spec (x (hcover i).choose).val,by
      intro g i j hij
      let a := (hcover i).choose
      let b := (hcover j).choose
      let u := (hcover i).choose_spec.choose
      let v := (hcover j).choose_spec.choose
      have hu : u • rep a = i := (hcover i).choose_spec.choose_spec
      have hv : v • rep b = j := (hcover j).choose_spec.choose_spec
      have hgu : (g*u) • rep a = j := by rw [mul_smul,hu,hij]
      change T.move g i j hij (T.move u (rep a) i hu (x a).val) =
        T.move v (rep b) j hv (x b).val
      rw [← T.mul_apply g u (rep a) i j hu hij]
      exact T.representative_move_eq rep hsep x a b (g*u) v j hgu hv⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    exact map_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    funext i
    exact map_smul _ _ _

@[simp] theorem orbitEvaluation_extend (x : ∀ a : J, T.stabilizerFixed (rep a)) :
    T.orbitEvaluation rep (T.orbitExtend rep hsep hcover x) = x := by
  funext a
  apply Subtype.ext
  change T.move (hcover (rep a)).choose_spec.choose (rep (hcover (rep a)).choose) (rep a)
    (hcover (rep a)).choose_spec.choose_spec (x (hcover (rep a)).choose).val = (x a).val
  rw [T.representative_move_eq rep hsep x (hcover (rep a)).choose a
    (hcover (rep a)).choose_spec.choose 1 (rep a)
    (hcover (rep a)).choose_spec.choose_spec (one_smul G (rep a)),T.one_apply]

@[simp] theorem orbitExtend_evaluation (x : T.invariantSections) :
    T.orbitExtend rep hsep hcover (T.orbitEvaluation rep x) = x := by
  apply Subtype.ext
  funext i
  exact x.property (hcover i).choose_spec.choose (rep (hcover i).choose) i
    (hcover i).choose_spec.choose_spec

/-- Full orbit/stabilizer decomposition of invariant sections, retaining literal
restriction to the selected representative in every component. -/
def orbitEvaluationEquiv : T.invariantSections ≃ₗ[R] ∀ a : J, T.stabilizerFixed (rep a) where
  __ := T.orbitEvaluation rep
  invFun := T.orbitExtend rep hsep hcover
  left_inv := T.orbitExtend_evaluation rep hsep hcover
  right_inv := T.orbitEvaluation_extend rep hsep hcover

@[simp] theorem orbitEvaluationEquiv_apply (x : T.invariantSections) (a : J) :
    (T.orbitEvaluationEquiv rep hsep hcover x a).val = x.val (rep a) := rfl

end KhanSL2.Factorization.FiberTransport

