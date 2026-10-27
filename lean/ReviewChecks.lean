module

public import KhanSL2.InjectivityMainStatement

@[expose] public section

/-! Statement-compatibility checks included in the combined project.

1. Restate the exact claimed theorem types.
2. Bridge the reworded `MainStatement` to the original (Lean 4.13) wording,
   copied verbatim from `sl2-cohomology-statement/KhanSL2/MainStatement.lean`.
3. Print axioms of everything stated here. -/

namespace KhanSL2.Review

open KhanSL2

/-- The original statement, verbatim from the frozen statement project. -/
def MainStatementV1 : Prop :=
  ∃ Φ : GradedDifferentialPVAEquiv
      sourceData Source.bracket targetData targetBracket,
    Φ.toLinearEquiv (Source.X 0) = xClass ∧
    Φ.toLinearEquiv (Source.Y 0) = yClass

theorem mainStatement_iff_v1 : MainStatement ↔ MainStatementV1 := by
  constructor
  · intro h
    exact ⟨h.toEquiv, phi_X0, phi_Y0⟩
  · rintro ⟨Φ, hx, hy⟩
    have hΦ : Φ.toLinearEquiv.toLinearMap = phi :=
      phi_unique _ Φ.map_one (fun a b => Φ.map_mul a b) Φ.map_translation hx hy
    exact IsGradedDifferentialPVAIsomorphism.iff_exists_equiv.2 ⟨Φ, hΦ⟩

/-- With injectivity, the original wording is equivalent to surjectivity. -/
theorem mainStatementV1_iff_surjective : MainStatementV1 ↔ Function.Surjective phi :=
  mainStatement_iff_v1.symm.trans mainStatement_iff_surjective

end KhanSL2.Review

#check (KhanSL2.phi_injective : Function.Injective KhanSL2.phi)
#check (KhanSL2.mainStatement_iff_surjective :
  KhanSL2.MainStatement ↔ Function.Surjective KhanSL2.phi)
#print KhanSL2.MainStatement
#print axioms KhanSL2.phi_injective
#print axioms KhanSL2.Review.mainStatement_iff_v1
#print axioms KhanSL2.Review.mainStatementV1_iff_surjective
