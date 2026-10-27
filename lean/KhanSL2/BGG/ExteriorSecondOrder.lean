module

public import KhanSL2.ExteriorRing

@[expose] public section

/-!
# Extensionality for operators of second order on an exterior algebra

For an even operator vanishing at one, the second-order Leibniz condition
says that its multiplication defect against each odd generator is an odd
derivation. Such operators are determined by their values on one, generators,
and pairs of generators. This formulation avoids any finite-rank assumption.
-/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

/-- Extensionality for maps satisfying the odd Leibniz rule. -/
theorem oddLeibniz_ext (D E : Exterior α →ₗ[ℂ] Exterior α)
    (hD : ∀ u v, D (u * v) = D u * v + parityLinear u * D v)
    (hE : ∀ u v, E (u * v) = E u * v + parityLinear u * E v)
    (h1 : D 1 = E 1) (hgen : ∀ a, D (generator a) = E (generator a)) : D = E := by
  apply LinearMap.ext
  intro u
  induction u using induction_on (GeneratorOrder.code (α := α)) with
  | hzero => simp
  | hone => exact h1
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen a u hu =>
    change D (generator a * u) = E (generator a * u)
    rw [hD, hE, hgen, hu]

/-- The first multiplication defect of an even linear operator against an odd generator. -/
def generatorDefect (D : Exterior α →ₗ[ℂ] Exterior α) (a : α) :
    Exterior α →ₗ[ℂ] Exterior α :=
  D.comp (wedgeLinear (GeneratorOrder.code (α := α)) (generator a)) -
    wedgeLinear (GeneratorOrder.code (α := α)) (D (generator a)) -
    (wedgeLinear (GeneratorOrder.code (α := α)) (generator a)).comp D

@[simp] theorem generatorDefect_apply (D : Exterior α →ₗ[ℂ] Exterior α)
    (a : α) (u : Exterior α) :
    generatorDefect D a u = D (generator a * u) - D (generator a) * u - generator a * D u := rfl

/-- The reduced second-order Leibniz condition for an even operator. When the
operator vanishes at one, this is the usual order-at-most-two condition,
expressed using the algebra's odd generating family. -/
def HasSecondOrderLeibniz (D : Exterior α →ₗ[ℂ] Exterior α) : Prop :=
  ∀ a u v, generatorDefect D a (u * v) =
    generatorDefect D a u * v + parityLinear u * generatorDefect D a v

/-- Second-order operators agree if their values agree on one, generators, and
pairs of generators. The second-order Leibniz conditions are explicit hypotheses. -/
theorem secondOrder_ext (D E : Exterior α →ₗ[ℂ] Exterior α)
    (hD : HasSecondOrderLeibniz D) (hE : HasSecondOrderLeibniz E)
    (h1 : D 1 = E 1) (hgen : ∀ a, D (generator a) = E (generator a))
    (hpair : ∀ a b, D (generator a * generator b) = E (generator a * generator b)) : D = E := by
  have hdefect (a : α) : generatorDefect D a = generatorDefect E a := by
    apply oddLeibniz_ext _ _ (hD a) (hE a)
    · simp only [generatorDefect_apply, mul_one, hgen, h1]
    · intro b
      simp only [generatorDefect_apply, hpair, hgen]
  apply LinearMap.ext
  intro u
  induction u using induction_on (GeneratorOrder.code (α := α)) with
  | hzero => simp
  | hone => exact h1
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen a u hu =>
    change D (generator a * u) = E (generator a * u)
    have h := congrArg (fun f : Exterior α →ₗ[ℂ] Exterior α => f u) (hdefect a)
    simp only [generatorDefect_apply, hgen, hu] at h
    exact sub_left_inj.mp (sub_left_inj.mp h)

/-- A second-order operator vanishing in exterior degrees zero, one, and two vanishes everywhere. -/
theorem secondOrder_eq_zero (D : Exterior α →ₗ[ℂ] Exterior α)
    (hD : HasSecondOrderLeibniz D) (h1 : D 1 = 0)
    (hgen : ∀ a, D (generator a) = 0)
    (hpair : ∀ a b, D (generator a * generator b) = 0) : D = 0 := by
  apply secondOrder_ext D 0 hD
  · intro a u v
    simp [generatorDefect_apply]
  · exact h1
  · exact hgen
  · exact hpair

end KhanSL2.FiniteExterior
