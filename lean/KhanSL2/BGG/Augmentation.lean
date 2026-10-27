module

public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Tactic.Abel

@[expose] public section

/-! The augmentation ideal of a universal enveloping algebra, as a left
module. Lie generators suffice to generate this ideal as a left ideal. -/

noncomputable section

namespace KhanSL2.BGG.UE

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "A" => UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The augmentation sends every Lie generator to zero. -/
def augmentation : A →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

@[simp] theorem augmentation_ι (x : L) :
    augmentation R L (UniversalEnvelopingAlgebra.ι R x) = 0 := by
  exact UniversalEnvelopingAlgebra.lift_ι_apply R _ x

@[simp] theorem augmentation_algebraMap (r : R) :
    augmentation R L (algebraMap R A r) = r := by
  simp [augmentation]

theorem augmentation_surjective : Function.Surjective (augmentation R L) := by
  intro r
  exact ⟨algebraMap R A r, augmentation_algebraMap R L r⟩

/-- An algebra-generation induction principle, without any PBW assumption. -/
@[elab_as_elim] theorem induction {C : A → Prop}
    (scalar : ∀ r, C (algebraMap R A r))
    (generator : ∀ x, C (UniversalEnvelopingAlgebra.ι R x))
    (mul : ∀ a b, C a → C b → C (a * b))
    (add : ∀ a b, C a → C b → C (a + b)) (a : A) : C a := by
  have hsurj : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom R L) :=
    RingCon.mkₐ_surjective _
  obtain ⟨t, rfl⟩ := hsurj a
  induction t using TensorAlgebra.induction with
  | algebraMap r => simpa using scalar r
  | ι x => exact generator x
  | mul a b ha hb => simpa using mul _ _ ha hb
  | add a b ha hb => simpa using add _ _ ha hb

/-- The augmentation kernel, with its left multiplication module structure. -/
def leftKernel : Submodule A A where
  carrier := {a | augmentation R L a = 0}
  zero_mem' := map_zero _
  add_mem' := by
    intro a b ha hb
    change augmentation R L (a + b) = 0
    change augmentation R L a = 0 at ha
    change augmentation R L b = 0 at hb
    simp only [map_add, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    change augmentation R L (a * b) = 0
    rw [map_mul, hb, mul_zero]

@[simp] theorem mem_leftKernel (a : A) :
    a ∈ leftKernel R L ↔ augmentation R L a = 0 := Iff.rfl

/-- Every element differs from its scalar augmentation by a left combination
of Lie generators. This is the form needed for augmentation exactness. -/
theorem sub_augmentation_mem (I : Submodule A A)
    (hI : ∀ x : L, UniversalEnvelopingAlgebra.ι R x ∈ I) (a : A) :
    a - algebraMap R A (augmentation R L a) ∈ I := by
  induction a using induction R L with
  | scalar r => simp
  | generator x => simpa only [augmentation_ι, map_zero, sub_zero] using hI x
  | add a b ha hb =>
      simpa only [map_add, add_sub_add_comm] using I.add_mem ha hb
  | mul a b ha hb =>
      have h₁ := I.smul_mem a hb
      have h₂ := I.smul_mem (algebraMap R A (augmentation R L b)) ha
      have heq :
          a * b - algebraMap R A (augmentation R L (a * b)) =
            a * (b - algebraMap R A (augmentation R L b)) +
              algebraMap R A (augmentation R L b) *
                (a - algebraMap R A (augmentation R L a)) := by
        simp only [map_mul, mul_sub]
        rw [Algebra.commutes (augmentation R L b) a,
          Algebra.commutes (augmentation R L b)
            (algebraMap R A (augmentation R L a))]
        abel
      rw [heq]
      exact I.add_mem h₁ h₂

theorem leftKernel_le (I : Submodule A A)
    (hI : ∀ x : L, UniversalEnvelopingAlgebra.ι R x ∈ I) :
    leftKernel R L ≤ I := by
  intro a ha
  have h := sub_augmentation_mem R L I hI a
  change augmentation R L a = 0 at ha
  simpa only [ha, map_zero, sub_zero] using h

theorem leftKernel_eq_span :
    leftKernel R L = Submodule.span A (Set.range (UniversalEnvelopingAlgebra.ι R)) := by
  apply le_antisymm
  · exact leftKernel_le R L _ fun x => Submodule.subset_span ⟨x, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact augmentation_ι R L x

/-- Pulling a left ideal back along the Lie inclusion gives a Lie subalgebra:
left multiplication suffices because the bracket is a commutator. -/
def liePreimage (I : Submodule A A) : LieSubalgebra R L where
  carrier := {x | UniversalEnvelopingAlgebra.ι R x ∈ I}
  zero_mem' := by
    change UniversalEnvelopingAlgebra.ι R (0 : L) ∈ I
    simp
  add_mem' := by
    intro x y hx hy
    change UniversalEnvelopingAlgebra.ι R (x + y) ∈ I
    simpa only [map_add] using I.add_mem hx hy
  smul_mem' := by
    intro r x hx
    change UniversalEnvelopingAlgebra.ι R (r • x) ∈ I
    have h := I.smul_mem (algebraMap R A r) hx
    simpa only [map_smul, Algebra.smul_def, smul_eq_mul] using h
  lie_mem' := by
    intro x y hx hy
    change UniversalEnvelopingAlgebra.ι R ⁅x, y⁆ ∈ I
    rw [(UniversalEnvelopingAlgebra.ι R).map_lie]
    change UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
      UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x ∈ I
    exact I.sub_mem (I.smul_mem _ hy) (I.smul_mem _ hx)

@[simp] theorem mem_liePreimage (I : Submodule A A) (x : L) :
    x ∈ liePreimage R L I ↔ UniversalEnvelopingAlgebra.ι R x ∈ I := Iff.rfl

/-- A generating set for the Lie algebra also generates the augmentation
kernel as a left ideal in its enveloping algebra. -/
theorem leftKernel_le_of_lieSpan_eq_top (S : Set L)
    (hS : LieSubalgebra.lieSpan R L S = ⊤) (I : Submodule A A)
    (hI : ∀ x ∈ S, UniversalEnvelopingAlgebra.ι R x ∈ I) :
    leftKernel R L ≤ I := by
  apply leftKernel_le R L I
  have hle : LieSubalgebra.lieSpan R L S ≤ liePreimage R L I :=
    LieSubalgebra.lieSpan_le.mpr hI
  intro x
  exact hle (by rw [hS]; trivial)

theorem leftKernel_eq_span_of_lieSpan_eq_top (S : Set L)
    (hS : LieSubalgebra.lieSpan R L S = ⊤) :
    leftKernel R L =
      Submodule.span A ((UniversalEnvelopingAlgebra.ι R) '' S) := by
  apply le_antisymm
  · apply leftKernel_le_of_lieSpan_eq_top R L S hS
    intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, _, rfl⟩
    exact augmentation_ι R L x

end KhanSL2.BGG.UE
