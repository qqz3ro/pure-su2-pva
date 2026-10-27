module

public import KhanSL2.Injectivity
public import KhanSL2.MainStatement

@[expose] public section

namespace KhanSL2

/-- After injectivity, the original isomorphism proposition is equivalent to
surjectivity of the same specified map. -/
theorem mainStatement_iff_surjective : MainStatement ↔ Function.Surjective phi := by
  rw [mainStatement_iff_bijective]
  exact ⟨fun h => h.2, fun h => ⟨phi_injective, h⟩⟩

end KhanSL2
