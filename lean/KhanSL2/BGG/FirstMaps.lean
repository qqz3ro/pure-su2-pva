module

public import KhanSL2.BGG.Current
public import KhanSL2.BGG.Augmentation
public import KhanSL2.BGG.Vacuum
public import Mathlib.Algebra.Lie.Abelian

@[expose] public section

/-!
# The first two relative induced modules and their specified maps

`P0` is induced from the trivial constant-sl₂ module; `P1` is induced from
its adjoint module. Its coefficient generators map to mode-one currents. The differential
sends `a ⊗ x` to `a (z x) ⊗ 1`, and the augmentation is the enveloping-algebra
augmentation on the cyclic vacuum. All balancing and equivariance laws below
are proved for these concrete maps.
-/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing


abbrev Enveloping := UniversalEnvelopingAlgebra ℂ Current

/-- The image of a constant current in the enveloping algebra. -/
def constGenerator (x : G) : Enveloping := UniversalEnvelopingAlgebra.ι ℂ (constant x)

/-- The image of a mode-one current in the enveloping algebra. -/
def stepGenerator : G →ₗ[ℂ] Enveloping :=
  (UniversalEnvelopingAlgebra.ι ℂ).toLinearMap.comp (mode 1)

@[simp] theorem stepGenerator_apply (x : G) :
    stepGenerator x = UniversalEnvelopingAlgebra.ι ℂ (mode 1 x) := rfl

/-- The adjoint coefficient module for the first induced term. -/
def adjointAction (x : G) : G →ₗ[ℂ] G := LieAlgebra.ad ℂ G x

abbrev P0 := Vacuum.Model (R := ℂ) constGenerator
abbrev P1 := Induced.Model constGenerator adjointAction

def p0Vacuum : P0 := Vacuum.vacuum constGenerator

def p0Cyclic : Enveloping →ₗ[Enveloping] P0 := Vacuum.cyclic constGenerator

def p1Generator : G →ₗ[ℂ] P1 := Induced.of constGenerator adjointAction

@[simp] theorem p0Cyclic_apply (a : Enveloping) : p0Cyclic a = a • p0Vacuum := rfl

theorem p0Cyclic_surjective : Function.Surjective p0Cyclic :=
  Vacuum.cyclic_surjective constGenerator

@[simp] theorem p0Cyclic_const (x : G) : p0Cyclic (constGenerator x) = 0 :=
  Vacuum.cyclic_inc_zero constGenerator x

@[simp] theorem const_smul_vacuum (x : G) : constGenerator x • p0Vacuum = 0 :=
  Vacuum.inc_smul_vacuum constGenerator x

theorem stepGenerator_lie (x y : G) :
    stepGenerator ⁅x, y⁆ =
      constGenerator x * stepGenerator y - stepGenerator y * constGenerator x := by
  change UniversalEnvelopingAlgebra.ι ℂ (mode 1 ⁅x, y⁆) =
    ⁅UniversalEnvelopingAlgebra.ι ℂ (mode 0 x),
      UniversalEnvelopingAlgebra.ι ℂ (mode 1 y)⁆
  rw [← (UniversalEnvelopingAlgebra.ι ℂ).map_lie, mode_lie]

def d1Coefficient : G →ₗ[ℂ] P0 := stepGenerator.smulRight p0Vacuum

theorem d1Coefficient_equivariant (x y : G) :
    d1Coefficient (adjointAction x y) = constGenerator x • d1Coefficient y := by
  change stepGenerator ⁅x, y⁆ • p0Vacuum =
    constGenerator x • (stepGenerator y • p0Vacuum)
  rw [stepGenerator_lie, sub_smul, mul_smul, mul_smul,
    const_smul_vacuum, smul_zero, sub_zero]

/-- The specified first BGG differential. -/
def d1 : P1 →ₗ[Enveloping] P0 :=
  Induced.lift constGenerator adjointAction d1Coefficient d1Coefficient_equivariant

@[simp] theorem d1_generator (x : G) :
    d1 (p1Generator x) = p0Cyclic (stepGenerator x) :=
  Induced.lift_of _ _ _ _ _

/-- The defining tensor formula, after passage to the actual induced quotient. -/
theorem d1_mk_tmul (a : Enveloping) (x : G) :
    d1 (Induced.mk constGenerator adjointAction (a ⊗ₜ[ℂ] x)) =
      p0Cyclic (a * stepGenerator x) := by
  rw [Induced.mk_tmul, map_smul]
  change a • d1 (p1Generator x) = p0Cyclic (a * stepGenerator x)
  rw [d1_generator, ← map_smul, smul_eq_mul]

/-- The specified augmentation of the vacuum module. -/
def epsilon : P0 →ₗ[ℂ] ℂ :=
  Vacuum.augmentationMap (UE.augmentation ℂ Current) constGenerator
    (fun x => UE.augmentation_ι ℂ Current (constant x))

@[simp] theorem epsilon_cyclic (a : Enveloping) :
    epsilon (p0Cyclic a) = UE.augmentation ℂ Current a :=
  Vacuum.augmentationMap_cyclic _ _ _ a

@[simp] theorem epsilon_vacuum : epsilon p0Vacuum = 1 :=
  Vacuum.augmentationMap_vacuum _ _ _

theorem epsilon_surjective : Function.Surjective epsilon :=
  Vacuum.augmentationMap_surjective _ _ _

theorem epsilon_smul (a : Enveloping) (q : P0) :
    epsilon (a • q) = UE.augmentation ℂ Current a * epsilon q :=
  Vacuum.augmentationMap_smul _ _ _ a q

@[simp] theorem epsilon_d1_generator (x : G) : epsilon (d1 (p1Generator x)) = 0 := by
  rw [d1_generator, epsilon_cyclic]
  exact UE.augmentation_ι ℂ Current (mode 1 x)

@[simp] theorem epsilon_d1 (q : P1) : epsilon (d1 q) = 0 := by
  refine Induced.induction_on constGenerator adjointAction q ?_ ?_
  · intro a x
    change epsilon (d1 (a • p1Generator x)) = 0
    rw [map_smul, epsilon_smul, epsilon_d1_generator, mul_zero]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

attribute [local instance] LieRingModule.ofAssociativeModule

instance p0LieRingModule : LieRingModule Current P0 :=
  LieRingModule.compLieHom P0 (UniversalEnvelopingAlgebra.ι ℂ)

instance p1LieRingModule : LieRingModule Current P1 :=
  LieRingModule.compLieHom P1 (UniversalEnvelopingAlgebra.ι ℂ)

instance p0LieModule : LieModule ℂ Current P0 := by
  let := LieModule.ofAssociativeModule (R := ℂ) (A := Enveloping) (M := P0)
  exact LieModule.compLieHom P0 (UniversalEnvelopingAlgebra.ι ℂ)

instance p1LieModule : LieModule ℂ Current P1 := by
  let := LieModule.ofAssociativeModule (R := ℂ) (A := Enveloping) (M := P1)
  exact LieModule.compLieHom P1 (UniversalEnvelopingAlgebra.ι ℂ)

@[simp] theorem p0_lie (x : Current) (q : P0) :
    ⁅x, q⁆ = (UniversalEnvelopingAlgebra.ι ℂ x : Enveloping) • q := rfl

@[simp] theorem p1_lie (x : Current) (q : P1) :
    ⁅x, q⁆ = (UniversalEnvelopingAlgebra.ι ℂ x : Enveloping) • q := rfl

/-- The first differential as a homomorphism of current Lie modules. -/
def d1Lie : P1 →ₗ⁅ℂ, Current⁆ P0 where
  toLinearMap := d1.restrictScalars ℂ
  map_lie' {x} {q} := d1.map_smul (UniversalEnvelopingAlgebra.ι ℂ x) q

/-- The augmentation as a homomorphism to the actual trivial scalar module. -/
def epsilonLie : P0 →ₗ⁅ℂ, Current⁆ TrivialLieModule ℂ Current ℂ where
  toLinearMap := (TrivialLieModule.equiv ℂ Current ℂ).symm.toLinearMap.comp epsilon
  map_lie' {x} {q} := by
    change epsilon ((UniversalEnvelopingAlgebra.ι ℂ x : Enveloping) • q) = 0
    rw [epsilon_smul, UE.augmentation_ι, zero_mul]

end KhanSL2.BGG
