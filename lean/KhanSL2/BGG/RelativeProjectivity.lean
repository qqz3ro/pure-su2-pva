module

public import KhanSL2.BGG.Induced

@[expose] public section

/-! Relative projectivity of the constructed induced modules. -/

noncomputable section

namespace KhanSL2.BGG.Induced

variable {R A G M N N' : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

/-- An induced module lifts through every `A`-linear epimorphism equipped with
an `R`-linear section equivariant for the chosen generators. This is the
relative projectivity property used for Lie-induced resolutions. -/
theorem exists_lift_of_equivariant_section
    (inc : G → A) (act : G → M →ₗ[R] M)
    (π : N →ₗ[A] N') (s : N' →ₗ[R] N)
    (hs : ∀ n, π (s n) = n)
    (hs_inc : ∀ x n, s (inc x • n) = inc x • s n)
    (F : Model inc act →ₗ[A] N') :
    ∃ F' : Model inc act →ₗ[A] N, π.comp F' = F := by
  let f : M →ₗ[R] N := s.comp ((F.restrictScalars R).comp (of inc act))
  have hf : ∀ x m, f (act x m) = inc x • f m := by
    intro x m
    change s (F (of inc act (act x m))) = inc x • s (F (of inc act m))
    rw [← inc_smul_of, map_smul, hs_inc]
  refine ⟨lift inc act f hf, ?_⟩
  apply hom_ext inc act
  intro m
  change π (lift inc act f hf (of inc act m)) = F (of inc act m)
  rw [lift_of]
  exact hs _

end KhanSL2.BGG.Induced
