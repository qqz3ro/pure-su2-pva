module

public import KhanSL2.BGG.ExteriorSecondOrder
public import KhanSL2.ExteriorSupercomm
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! Explicit Leibniz calculations for first- and second-order exterior operators. -/

noncomputable section
namespace KhanSL2.FiniteExterior
variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

abbrev multiply (f : Exterior α) : Module.End ℂ (Exterior α) :=
  wedgeLinear (GeneratorOrder.code (α := α)) f

@[simp] theorem multiply_apply (f u : Exterior α) : multiply f u = f * u := rfl

def HasOddLeibniz (D : Module.End ℂ (Exterior α)) : Prop :=
  ∀ u v, D (u*v) = D u*v + parityLinear u*D v

def HasEvenLeibniz (D : Module.End ℂ (Exterior α)) : Prop :=
  ∀ u v, D (u*v) = D u*v + u*D v

def PreservesParity (D : Module.End ℂ (Exterior α)) : Prop :=
  ∀ u, D (parityLinear u) = parityLinear (D u)

def ReversesParity (D : Module.End ℂ (Exterior α)) : Prop :=
  ∀ u, D (parityLinear u) = -parityLinear (D u)

theorem parity_mul (u v : Exterior α) :
    parityLinear (u*v) = parityLinear u*parityLinear v := (parity (α := α)).map_mul u v

theorem odd_generator_even (D : Module.End ℂ (Exterior α)) (hp : ReversesParity D) (a : α) :
    parityLinear (D (generator a)) = D (generator a) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  have h := hp (generator a)
  rw [parity_generator, map_neg] at h
  exact (neg_injective h).symm

omit [DecidableEq α] [GeneratorOrder α] in
theorem even_generator_odd (D : Module.End ℂ (Exterior α)) (hp : PreservesParity D) (a : α) :
    parityLinear (D (generator a)) = -D (generator a) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  simpa only [parity_generator, map_neg] using (hp (generator a)).symm

theorem even_mul_comm (f : Exterior α) (hf : parityLinear f = f) (u : Exterior α) :
    u*f = f*u := wedge_comm_of_parity_even _ GeneratorOrder.code_injective f hf u

theorem odd_mul_comm (f : Exterior α) (hf : parityLinear f = -f) (u : Exterior α) :
    u*f = f*parityLinear u := wedge_comm_of_parity_odd _ GeneratorOrder.code_injective f hf u

theorem HasOddLeibniz.sub {D E : Module.End ℂ (Exterior α)}
    (hD : HasOddLeibniz D) (hE : HasOddLeibniz E) : HasOddLeibniz (D-E) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro u v
  simp only [LinearMap.sub_apply, hD u v, hE u v]
  noncomm_ring

theorem HasOddLeibniz.even_multiply {D : Module.End ℂ (Exterior α)}
    (hD : HasOddLeibniz D) (f : Exterior α) (hf : parityLinear f = f) :
    HasOddLeibniz ((multiply f).comp D) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro u v
  simp only [LinearMap.comp_apply, multiply_apply, hD u v, mul_add]
  rw [← mul_assoc (parityLinear u) f, even_mul_comm f hf]
  simp only [mul_assoc]

theorem HasEvenLeibniz.odd_multiply {D : Module.End ℂ (Exterior α)}
    (hD : HasEvenLeibniz D) (f : Exterior α) (hf : parityLinear f = -f) :
    HasOddLeibniz ((multiply f).comp D) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro u v
  simp only [LinearMap.comp_apply, multiply_apply, hD u v, mul_add]
  rw [← mul_assoc (parityLinear u) f, odd_mul_comm f hf, parity_involutive]
  simp only [mul_assoc]

theorem HasSecondOrderLeibniz.add {D E : Module.End ℂ (Exterior α)}
    (hD : HasSecondOrderLeibniz D) (hE : HasSecondOrderLeibniz E) :
    HasSecondOrderLeibniz (D+E) := by
  intro a u v
  have h (w : Exterior α) : generatorDefect (D+E) a w =
      generatorDefect D a w + generatorDefect E a w := by
    simp only [generatorDefect_apply, LinearMap.add_apply]
    noncomm_ring
  simp only [h, hD a u v, hE a u v]
  noncomm_ring

theorem HasSecondOrderLeibniz.smul {D : Module.End ℂ (Exterior α)}
    (hD : HasSecondOrderLeibniz D) (r : ℂ) : HasSecondOrderLeibniz (r • D) := by
  intro a u v
  have h := congrArg (fun x : Exterior α => r • x) (hD a u v)
  simpa only [generatorDefect_apply, LinearMap.smul_apply, smul_sub, smul_add,
    smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub] using h

theorem HasEvenLeibniz.secondOrder {D : Module.End ℂ (Exterior α)}
    (hD : HasEvenLeibniz D) : HasSecondOrderLeibniz D := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro a u v
  simp only [generatorDefect_apply, hD (generator a), add_sub_cancel_right,
    sub_self, zero_mul, mul_zero, add_zero]
  noncomm_ring

/-- Composing two odd derivations and multiplying by an even coefficient has order at most two. -/
theorem secondOrder_odd_odd (D E : Module.End ℂ (Exterior α))
    (hD : HasOddLeibniz D) (hE : HasOddLeibniz E)
    (hpD : ReversesParity D) (hpE : ReversesParity E)
    (f : Exterior α) (hf : parityLinear f = f) :
    HasSecondOrderLeibniz ((multiply f).comp (D.comp E)) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro a
  have hDa := odd_generator_even D hpD a
  have hEa := odd_generator_even E hpE a
  have hdef : generatorDefect ((multiply f).comp (D.comp E)) a =
      (multiply (f * E (generator a))).comp D -
      (multiply (f * D (generator a))).comp E := by
    apply LinearMap.ext
    intro u
    simp only [generatorDefect_apply, LinearMap.comp_apply, multiply_apply,
      LinearMap.sub_apply, hE (generator a), map_add, hD, parity_generator,
      hEa, map_neg, parityLinear.map_neg, parity_generator, neg_neg]
    rw [← mul_assoc (generator a) f, even_mul_comm f hf]
    noncomm_ring
  rw [hdef]
  exact (HasOddLeibniz.even_multiply hD _ (by rw [parity_mul, hf, hEa])).sub
    (HasOddLeibniz.even_multiply hE _ (by rw [parity_mul, hf, hDa]))

/-- An odd coefficient times an odd-after-even composition also has order at most two. -/
theorem secondOrder_odd_even (D E : Module.End ℂ (Exterior α))
    (hD : HasOddLeibniz D) (hE : HasEvenLeibniz E)
    (hpD : ReversesParity D) (hpE : PreservesParity E)
    (f : Exterior α) (hf : parityLinear f = -f) :
    HasSecondOrderLeibniz ((multiply f).comp (D.comp E)) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro a
  have hDa := odd_generator_even D hpD a
  have hEa := even_generator_odd E hpE a
  have hdef : generatorDefect ((multiply f).comp (D.comp E)) a =
      (multiply (f * D (generator a))).comp E -
      (multiply (f * E (generator a))).comp D := by
    apply LinearMap.ext
    intro u
    simp only [generatorDefect_apply, LinearMap.comp_apply, multiply_apply,
      LinearMap.sub_apply, hE (generator a), map_add, hD, parity_generator, hEa]
    rw [← mul_assoc (generator a) f, odd_mul_comm f hf, parity_generator]
    noncomm_ring
  rw [hdef]
  exact (HasEvenLeibniz.odd_multiply hE _ (by rw [parity_mul, hf, hDa, neg_mul])).sub
    (HasOddLeibniz.even_multiply hD _ (by rw [parity_mul, hf, hEa, neg_mul_neg]))

/-- An odd coefficient times an even-after-odd composition has order at most two. -/
theorem secondOrder_even_odd (D E : Module.End ℂ (Exterior α))
    (hD : HasEvenLeibniz D) (hE : HasOddLeibniz E)
    (hpD : PreservesParity D) (hpE : ReversesParity E)
    (f : Exterior α) (hf : parityLinear f = -f) :
    HasSecondOrderLeibniz ((multiply f).comp (D.comp E)) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro a
  have hDa := even_generator_odd D hpD a
  have hEa := odd_generator_even E hpE a
  have hdef : generatorDefect ((multiply f).comp (D.comp E)) a =
      (multiply (f * E (generator a))).comp D -
      (multiply (f * D (generator a))).comp E := by
    apply LinearMap.ext
    intro u
    simp only [generatorDefect_apply, LinearMap.comp_apply, multiply_apply,
      LinearMap.sub_apply, hE (generator a), map_add, hD, parity_generator, map_neg]
    rw [← mul_assoc (generator a) f, odd_mul_comm f hf, parity_generator]
    noncomm_ring
  rw [hdef]
  exact (HasEvenLeibniz.odd_multiply hD _ (by rw [parity_mul, hf, hEa, neg_mul])).sub
    (HasOddLeibniz.even_multiply hE _ (by rw [parity_mul, hf, hDa, neg_mul_neg]))


/-- The anticommutator of two odd derivations satisfies the even Leibniz rule. -/
theorem odd_anticommutator_even (D E : Module.End ℂ (Exterior α))
    (hD : HasOddLeibniz D) (hE : HasOddLeibniz E)
    (hpD : ReversesParity D) (hpE : ReversesParity E) :
    HasEvenLeibniz (D.comp E + E.comp D) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro u v
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hD, hE, map_add,
    hpD, hpE, parity_involutive]
  noncomm_ring

theorem odd_anticommutator_parity (D E : Module.End ℂ (Exterior α))
    (hpD : ReversesParity D) (hpE : ReversesParity E) :
    PreservesParity (D.comp E + E.comp D) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro u
  simp only [LinearMap.add_apply, LinearMap.comp_apply, hpD, hpE, map_neg,
    neg_neg, map_add]

theorem HasSecondOrderLeibniz.sub {D E : Module.End ℂ (Exterior α)}
    (hD : HasSecondOrderLeibniz D) (hE : HasSecondOrderLeibniz E) :
    HasSecondOrderLeibniz (D-E) := by
  intro a u v
  have h (w : Exterior α) : generatorDefect (D-E) a w =
      generatorDefect D a w - generatorDefect E a w := by
    simp only [generatorDefect_apply, LinearMap.sub_apply]
    noncomm_ring
  simp only [h, hD a u v, hE a u v]
  noncomm_ring

/-- An explicit supercommutator expansion; its three terms each contain at most
    two derivation factors. No operator-order property is assumed. -/
theorem secondOrder_odd_boundary_summand (D E F : Module.End ℂ (Exterior α))
    (hD : HasOddLeibniz D) (hE : HasOddLeibniz E) (hF : HasOddLeibniz F)
    (hpD : ReversesParity D) (hpE : ReversesParity E) (hpF : ReversesParity F)
    (a : α) : HasSecondOrderLeibniz
      (D.comp ((multiply (generator a)).comp (E.comp F)) +
        ((multiply (generator a)).comp (E.comp F)).comp D) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  have hexpand : D.comp ((multiply (generator a)).comp (E.comp F)) +
      ((multiply (generator a)).comp (E.comp F)).comp D =
      (multiply (D (generator a))).comp (E.comp F) -
      (multiply (generator a)).comp ((D.comp E + E.comp D).comp F) +
      (multiply (generator a)).comp (E.comp (D.comp F + F.comp D)) := by
    apply LinearMap.ext
    intro u
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      multiply_apply, hD, parity_generator, map_add]
    noncomm_ring
  rw [hexpand]
  exact ((secondOrder_odd_odd E F hE hF hpE hpF _ (odd_generator_even D hpD a)).sub
    (secondOrder_even_odd _ F (odd_anticommutator_even D E hD hE hpD hpE)
      hF (odd_anticommutator_parity D E hpD hpE) hpF _ (parity_generator a))).add
    (secondOrder_odd_even E _ hE (odd_anticommutator_even D F hD hF hpD hpF)
      hpE (odd_anticommutator_parity D F hpD hpF) _ (parity_generator a))


theorem HasOddLeibniz.add {D E : Module.End ℂ (Exterior α)}
    (hD : HasOddLeibniz D) (hE : HasOddLeibniz E) : HasOddLeibniz (D+E) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro u v
  simp only [LinearMap.add_apply, hD u v, hE u v]
  noncomm_ring

/-- The composition of two parity-preserving even derivations has order at most two. -/
theorem secondOrder_even_even (D E : Module.End ℂ (Exterior α))
    (hD : HasEvenLeibniz D) (hE : HasEvenLeibniz E)
    (hpD : PreservesParity D) (hpE : PreservesParity E) :
    HasSecondOrderLeibniz (D.comp E) := by
  dsimp only [HasOddLeibniz, HasEvenLeibniz, PreservesParity, ReversesParity] at *
  intro a
  have hDa := even_generator_odd D hpD a
  have hEa := even_generator_odd E hpE a
  have hdef : generatorDefect (D.comp E) a =
      (multiply (E (generator a))).comp D +
      (multiply (D (generator a))).comp E := by
    apply LinearMap.ext
    intro u
    simp only [generatorDefect_apply, LinearMap.comp_apply, multiply_apply,
      LinearMap.add_apply, hE (generator a), map_add, hD]
    noncomm_ring
  rw [hdef]
  exact (HasEvenLeibniz.odd_multiply hD _ hEa).add (HasEvenLeibniz.odd_multiply hE _ hDa)

end KhanSL2.FiniteExterior
