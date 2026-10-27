module

public import KhanSL2.BGG.InducedScalarLift
public import KhanSL2.BGG.Augmentation
public import Mathlib.LinearAlgebra.TensorProduct.Associator

@[expose] public section

/-! A proved multiplication factorization gives the expected model of an induced module. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG.Induced.Split

variable {R A D G M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring D] [Algebra R D] [LieRing G] [LieAlgebra R G]
  [AddCommGroup M] [Module R M]
  [Module (UniversalEnvelopingAlgebra R G) M]
  [IsScalarTower R (UniversalEnvelopingAlgebra R G) M]

local notation "B" => UniversalEnvelopingAlgebra R G

/-- The action of every enveloping-algebra element satisfies the induced balancing law. -/
theorem of_balanced_ue (inc : G → A) (act : G → M →ₗ[R] M)
    (rightMap : B →ₐ[R] A)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m)
    (b : B) (m : M) : rightMap b • of inc act m = of inc act (b • m) := by
  induction b using UE.induction R G generalizing m with
  | scalar r =>
    rw [rightMap.commutes, algebraMap_smul, algebraMap_smul, map_smul]
  | generator x => rw [hinc, hact, inc_smul_of]
  | add a b ha hb => rw [map_add, add_smul, ha, hb, add_smul, map_add]
  | mul a b ha hb => rw [map_mul, mul_smul, hb, ha, mul_smul]

/-- The forward map is always the specified multiplication on coefficient generators. -/
def forward (inc : G → A) (act : G → M →ₗ[R] M) (leftMap : D →ₐ[R] A) :
    D ⊗[R] M →ₗ[R] Model inc act :=
  ((mk inc act).restrictScalars R).comp
    (TensorProduct.map leftMap.toLinearMap (LinearMap.id : M →ₗ[R] M))

omit [LieRing G] [LieAlgebra R G] [Module B M] [IsScalarTower R B M] in
@[simp] theorem forward_tmul (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (u : D) (m : M) :
    forward inc act leftMap (u ⊗ₜ[R] m) = leftMap u • of inc act m := by
  change mk inc act (leftMap u ⊗ₜ[R] m) = _
  exact mk_tmul inc act (leftMap u) m

/-- Resolve the ambient factor into a left factor and a coefficient-action factor. -/
def rawInverse (e : D ⊗[R] B ≃ₗ[R] A) : A ⊗[R] M →ₗ[R] D ⊗[R] M :=
  (TensorProduct.map (LinearMap.id : D →ₗ[R] D)
    (tensorLiftLinear (LinearMap.id : M →ₗ[R] M))).comp
      ((TensorProduct.assoc R D B M).toLinearMap.comp
        (TensorProduct.map e.symm.toLinearMap (LinearMap.id : M →ₗ[R] M)))

theorem rawInverse_product (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A)
    (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (u : D) (b : B) (m : M) :
    rawInverse e ((leftMap u * rightMap b) ⊗ₜ[R] m) = u ⊗ₜ[R] (b • m) := by
  rw [← he]
  simp only [rawInverse, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.assoc_tmul,
    LinearMap.id_apply, tensorLiftLinear_tmul]

theorem rawInverse_balanced (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A) (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m)
    (a : A) (x : G) (m : M) :
    rawInverse e ((a * inc x) ⊗ₜ[R] m) = rawInverse e (a ⊗ₜ[R] act x m) := by
  obtain ⟨t, rfl⟩ := e.surjective a
  induction t using TensorProduct.inductionOn with
  | tmul u b =>
    rw [he, ← hinc, mul_assoc, ← map_mul, rawInverse_product leftMap rightMap e he,
      rawInverse_product leftMap rightMap e he, mul_smul, hact]
  | add t s ht hs =>
    simp only [map_add, add_mul, TensorProduct.add_tmul, ht, hs]

/-- The inverse is well-defined on the full balancing quotient. -/
def backward (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A) (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m) :
    Model inc act →ₗ[R] D ⊗[R] M :=
  descend inc act (rawInverse e) (rawInverse_balanced inc act leftMap rightMap e he hinc hact)

@[simp] theorem backward_mk (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A) (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m)
    (t : A ⊗[R] M) :
    backward inc act leftMap rightMap e he hinc hact (mk inc act t) = rawInverse e t := rfl

theorem forward_rawInverse (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A) (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m)
    (a : A) (m : M) :
    forward inc act leftMap (rawInverse e (a ⊗ₜ[R] m)) = mk inc act (a ⊗ₜ[R] m) := by
  obtain ⟨t, rfl⟩ := e.surjective a
  induction t using TensorProduct.inductionOn with
  | tmul u b =>
    rw [he, rawInverse_product leftMap rightMap e he, forward_tmul,
      ← of_balanced_ue inc act rightMap hinc hact b m, mk_tmul, mul_smul]
  | add t s ht hs =>
    simp only [map_add, TensorProduct.add_tmul, ht, hs]

/-- A proved PBW multiplication factorization induces the claimed coefficient tensor model. -/
def equiv (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A) (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m) :
    D ⊗[R] M ≃ₗ[R] Model inc act := by
  let F := forward inc act leftMap
  let H := backward inc act leftMap rightMap e he hinc hact
  refine { F with invFun := H, left_inv := ?_, right_inv := ?_ }
  · intro t
    change H (F t) = t
    induction t using TensorProduct.inductionOn with
    | tmul u m =>
      change backward inc act leftMap rightMap e he hinc hact
        (mk inc act (leftMap u ⊗ₜ[R] m)) = u ⊗ₜ[R] m
      rw [backward_mk]
      simpa only [map_one, mul_one, one_smul] using
        rawInverse_product leftMap rightMap e he u 1 m
    | add t s ht hs => simp only [map_add, ht, hs]
  · intro q
    change F (H q) = q
    obtain ⟨t, rfl⟩ := mk_surjective inc act q
    change forward inc act leftMap (backward inc act leftMap rightMap e he hinc hact (mk inc act t)) = _
    rw [backward_mk]
    induction t using TensorProduct.inductionOn with
    | tmul a m => exact forward_rawInverse inc act leftMap rightMap e he hinc hact a m
    | add t s ht hs => simp only [map_add, ht, hs]

@[simp] theorem equiv_tmul (inc : G → A) (act : G → M →ₗ[R] M)
    (leftMap : D →ₐ[R] A) (rightMap : B →ₐ[R] A) (e : D ⊗[R] B ≃ₗ[R] A)
    (he : ∀ u b, e (u ⊗ₜ[R] b) = leftMap u * rightMap b)
    (hinc : ∀ x, rightMap (UniversalEnvelopingAlgebra.ι R x) = inc x)
    (hact : ∀ x m, (UniversalEnvelopingAlgebra.ι R x : B) • m = act x m)
    (u : D) (m : M) :
    equiv inc act leftMap rightMap e he hinc hact (u ⊗ₜ[R] m) = leftMap u • of inc act m :=
  forward_tmul inc act leftMap u m

end KhanSL2.BGG.Induced.Split
