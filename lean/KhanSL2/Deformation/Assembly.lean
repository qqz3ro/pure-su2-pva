module

public import KhanSL2.Deformation.LowDegree
public import KhanSL2.Conditional.Assembly

@[expose] public section

/-!
# Compatibility with the earlier two-field completion interface

The low-degree deformation step and the polynomial properties of the actual BGG complex
are proved. The canonical `RemainingInputs` now contains collision support alone.
`TwoRemainingInputs` is retained for compatibility; its polynomial field is redundant
because `polynomialBGGInput` supplies it unconditionally. The direct final endpoint is
`mainStatement_of_collisionSupport`.
-/

noncomputable section

namespace KhanSL2.Conditional

/-- Legacy container; the polynomial field is supplied by a proved theorem. -/
structure TwoRemainingInputs : Prop where
  polynomialBGG : PolynomialBGGInput
  collisionSupport : CollisionSupportStep

/-- The legacy container supplies the sole remaining collision-support hypothesis. -/
theorem TwoRemainingInputs.toRemainingInputs (H : TwoRemainingInputs) : RemainingInputs :=
  ⟨H.collisionSupport⟩

/-- The redundant legacy polynomial field can always be filled by its proof. -/
theorem remainingInputs_iff_two : RemainingInputs ↔ TwoRemainingInputs :=
  ⟨fun H => ⟨polynomialBGGInput, H.collisionSupport⟩, TwoRemainingInputs.toRemainingInputs⟩

theorem psi_injective_of_twoInputs (H : TwoRemainingInputs) (B p : ℕ) :
    Function.Injective (psi B p) :=
  psi_injective_of_inputs H.toRemainingInputs B p

theorem psiB_bijective_of_twoInputs (H : TwoRemainingInputs) (B p : ℕ) :
    Function.Bijective (Modules.psiB B p) :=
  psiB_bijective_of_inputs H.toRemainingInputs B p

/-- Legacy form of the completion theorem; the polynomial field is redundant. -/
theorem mainStatement_of_twoInputs (H : TwoRemainingInputs) : MainStatement :=
  mainStatement_of_inputs H.toRemainingInputs

end KhanSL2.Conditional
