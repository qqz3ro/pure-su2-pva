module

public import KhanSL2.BGG.Induced
public import Mathlib.Algebra.Module.LinearMap.End

@[expose] public section

set_option maxHeartbeats 40000

/-! The module induced from the trivial coefficient representation. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG.Vacuum

variable {R A G : Type*} [CommRing R] [Ring A] [Algebra R A]

def trivialAction : G → R →ₗ[R] R := fun _ => 0

abbrev Model (inc : G → A) := Induced.Model inc (trivialAction (R := R))

def vacuum (inc : G → A) : Model (R := R) inc := Induced.of inc (trivialAction (R := R)) 1

def cyclic (inc : G → A) : A →ₗ[A] Model (R := R) inc :=
  LinearMap.id.smulRight (vacuum (R := R) inc)

@[simp] theorem cyclic_apply (inc : G → A) (a : A) :
    cyclic (R := R) inc a = a • vacuum (R := R) inc := rfl

theorem of_eq_smul_vacuum (inc : G → A) (r : R) :
    Induced.of inc (trivialAction (R := R)) r = r • vacuum (R := R) inc := by
  rw [vacuum, ← map_smul]
  simp only [smul_eq_mul, mul_one]

@[simp] theorem inc_smul_vacuum (inc : G → A) (x : G) :
    inc x • vacuum (R := R) inc = 0 := by
  have h := Induced.inc_smul_of inc (trivialAction (R := R)) x 1
  simpa [vacuum, trivialAction] using h

@[simp] theorem cyclic_inc_zero (inc : G → A) (x : G) :
    cyclic (R := R) inc (inc x) = 0 :=
  inc_smul_vacuum inc x

theorem cyclic_surjective (inc : G → A) :
    Function.Surjective (cyclic (R := R) inc) := by
  intro q
  refine Induced.induction_on inc (trivialAction (R := R)) q ?_ ?_
  · intro a r
    refine ⟨a * algebraMap R A r, ?_⟩
    rw [cyclic_apply, mul_smul, algebraMap_smul, of_eq_smul_vacuum]
  · intro x y hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩


section Augmentation

variable (aug : A →ₐ[R] R)

/-- The scalar-valued augmentation. Its equivariance for the augmentation
character is proved by `augmentationMap_smul`. -/
def augmentationMap (inc : G → A) (hinc : ∀ x, aug (inc x) = 0) :
    Model (R := R) inc →ₗ[R] R := by
  letI : Module A R := Module.compHom R aug.toRingHom
  letI : IsScalarTower R A R := ⟨by
    intro r a c
    change aug (r • a) * c = r * (aug a * c)
    rw [map_smul, smul_eq_mul, mul_assoc]⟩
  exact (Induced.lift inc (trivialAction (R := R)) (LinearMap.id : R →ₗ[R] R) (by
    intro x r
    change 0 = aug (inc x) * r
    rw [hinc, zero_mul])).restrictScalars R


@[simp] theorem augmentationMap_mk_tmul (inc : G → A)
    (hinc : ∀ x, aug (inc x) = 0) (a : A) (r : R) :
    augmentationMap aug inc hinc (Induced.mk inc (trivialAction (R := R)) (a ⊗ₜ[R] r)) =
      aug a * r := rfl

@[simp] theorem augmentationMap_of (inc : G → A) (hinc : ∀ x, aug (inc x) = 0)
    (r : R) : augmentationMap aug inc hinc (Induced.of inc (trivialAction (R := R)) r) = r := by
  rw [Induced.of_apply, augmentationMap_mk_tmul, map_one, one_mul]

@[simp] theorem augmentationMap_vacuum (inc : G → A) (hinc : ∀ x, aug (inc x) = 0) :
    augmentationMap aug inc hinc (vacuum (R := R) inc) = 1 :=
  augmentationMap_of aug inc hinc 1

@[simp] theorem augmentationMap_cyclic (inc : G → A) (hinc : ∀ x, aug (inc x) = 0)
    (a : A) : augmentationMap aug inc hinc (cyclic (R := R) inc a) = aug a := by
  change augmentationMap aug inc hinc (a • Induced.of inc (trivialAction (R := R)) 1) = aug a
  rw [← Induced.mk_tmul, augmentationMap_mk_tmul, mul_one]


/-- Equivariance for the scalar representation afforded by `aug`. -/
theorem augmentationMap_smul (inc : G → A) (hinc : ∀ x, aug (inc x) = 0)
    (a : A) (q : Model (R := R) inc) :
    augmentationMap aug inc hinc (a • q) = aug a * augmentationMap aug inc hinc q := by
  obtain ⟨b, rfl⟩ := cyclic_surjective inc q
  rw [← (cyclic (R := R) inc).map_smul a b, smul_eq_mul, augmentationMap_cyclic, map_mul, augmentationMap_cyclic]

theorem augmentationMap_surjective (inc : G → A) (hinc : ∀ x, aug (inc x) = 0) :
    Function.Surjective (augmentationMap aug inc hinc) := by
  intro r
  exact ⟨Induced.of inc (trivialAction (R := R)) r, augmentationMap_of aug inc hinc r⟩

end Augmentation

end KhanSL2.BGG.Vacuum
