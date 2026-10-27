module

public import KhanSL2.Injectivity.ChainPairing
public import KhanSL2.Injectivity.CartanRestriction
public import KhanSL2.CanonicalMap

/-! Closed Cartan functionals act on the already constructed canonical map.
The formulas below concern that actual map, not a replacement presentation. -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

def descendCartanFunctional (f : Cartan.Cochain →ₗ[ℂ] ℂ)
    (hf : ∀ u, f (Cartan.q u) = 0) : Cohomology →ₗ[ℂ] ℂ :=
  descendFunctional (f.comp Cartan.restriction.toLinearMap)
    (annihilatesDifferential_comp Cartan.restriction.toLinearMap Cartan.q
      Cartan.restriction_q f hf)

@[simp] theorem descendCartanFunctional_classOf
    (f : Cartan.Cochain →ₗ[ℂ] ℂ) (hf : ∀ u, f (Cartan.q u) = 0)
    (u : Cochain) (hu : u ∈ relativeCycles) :
    descendCartanFunctional f hf (classOf u hu) = f (Cartan.restriction u) := rfl

theorem descendFunctional_translation_pow
    (f : Cochain →ₗ[ℂ] ℂ) (hf : AnnihilatesDifferential f)
    (n : ℕ) (u : Cochain) (hu : u ∈ relativeCycles) :
    descendFunctional f hf ((targetData.translation ^ n) (classOf u hu)) =
      f ((translation ^ n) u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ, Module.End.mul_apply, target_translation_classOf, hn,
      pow_succ, Module.End.mul_apply]

theorem descendCartanFunctional_phi_X
    (f : Cartan.Cochain →ₗ[ℂ] ℂ) (hf : ∀ u, f (Cartan.q u) = 0) (n : ℕ) :
    descendCartanFunctional f hf (phi (Source.X n)) =
      f ((Cartan.translation ^ n)
        (Cartan.generator (.neutral 0) * Cartan.generator (.cartan 0))) := by
  rw [phi_X]
  change descendFunctional _ _ ((targetData.translation ^ n)
    (classOf xRepresentative xRepresentative_mem_cycles)) = _
  rw [descendFunctional_translation_pow]
  change f (Cartan.restriction ((translation ^ n) xRepresentative)) = _
  rw [Cartan.restriction_translation_pow, Cartan.restriction_xRepresentative]

theorem descendCartanFunctional_phi_Y
    (f : Cartan.Cochain →ₗ[ℂ] ℂ) (hf : ∀ u, f (Cartan.q u) = 0) (n : ℕ) :
    descendCartanFunctional f hf (phi (Source.Y n)) =
      (-2 : ℂ) * f ((Cartan.translation ^ n)
        ((Cartan.generator (.neutral 0) * Cartan.generator (.plus 0)) *
          Cartan.generator (.minus 0))) := by
  rw [phi_Y]
  change descendFunctional _ _ ((targetData.translation ^ n)
    (classOf yRepresentative yRepresentative_mem_cycles)) = _
  rw [descendFunctional_translation_pow]
  change f (Cartan.restriction ((translation ^ n) yRepresentative)) = _
  rw [Cartan.restriction_translation_pow, Cartan.restriction_yRepresentative,
    map_smul, map_smul, smul_eq_mul]

end KhanSL2.Injectivity
