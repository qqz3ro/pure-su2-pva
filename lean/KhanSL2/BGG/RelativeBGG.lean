module

public import KhanSL2.BGG.TermResolutionEnergy
public import KhanSL2.BGG.TermResolutionAugmentation
public import KhanSL2.BGG.TermRelativeAdmissibility

@[expose] public section
noncomputable section
universe u v
namespace KhanSL2.BGG
open scoped RelativeCochains

/-- Relative projectivity of the prescribed induced terms: every map lifts through
a current-module epimorphism split by a constant-equivariant complex-linear section. -/
def TermsRelativelyProjective : Prop :=
  ∀ (p : ℕ) (N : Type u) (N' : Type v)
    [AddCommGroup N] [Module ℂ N] [Module Enveloping N] [IsScalarTower ℂ Enveloping N]
    [AddCommGroup N'] [Module ℂ N'] [Module Enveloping N'] [IsScalarTower ℂ Enveloping N'],
    ∀ (π : N →ₗ[Enveloping] N') (s : N' →ₗ[ℂ] N),
      (∀ n, π (s n) = n) →
      (∀ x n, s (constGenerator x • n) = constGenerator x • s n) →
      ∀ F : Term p →ₗ[Enveloping] N', ∃ F' : Term p →ₗ[Enveloping] N, π.comp F' = F

/-- Relative projectivity is proved for the actual induced quotients. -/
theorem termsRelativelyProjective : TermsRelativelyProjective.{u,v} := by
  intro p N N' _ _ _ _ _ _ _ _ π s hs hc F
  exact term_relative_projective p π s hs hc F

/-- A graded augmented exact resolution on the fixed relative affine BGG terms
`U(sl₂[z]) ⊗_{U(sl₂)} V(2p)[p(p+1)/2]`. Every listed property is proof data;
the construction below supplies all of it from the actual CE/Hodge/PBW proof. -/
structure RelativeBGGResolution where
  differential : ∀ p : ℕ, Term (p+1) →ₗ[Enveloping] Term p
  augmentation : Term 0 →ₗ[ℂ] ℂ
  square_zero : ∀ p x, differential p (differential (p+1) x) = 0
  augmentation_differential : ∀ x, augmentation (differential 0 x) = 0
  exact_positive : ∀ p, Function.Exact (differential (p+1)) (differential p)
  exact_zero : Function.Exact (differential 0) augmentation
  augmentation_surjective : Function.Surjective augmentation
  augmentation_equivariant : ∀ a x,
    augmentation (a • x) = UE.augmentation ℂ Current a * augmentation x
  differential_energy : ∀ p n x,
    x ∈ termPiece (p+1) n → differential p x ∈ termPiece p n
  augmentation_energy : ∀ n x, x ∈ termPiece 0 n → n ≠ 0 → augmentation x = 0
  relatively_projective : TermsRelativelyProjective.{u,v}
  relative_admissible :
    (∃ s : ℂ →ₗ[ℂ] Term 0, (∀ r, augmentation (s r) = r) ∧
      (∀ x r, constGenerator x • s r = 0) ∧ (∀ r, s r ∈ termPiece 0 0)) ∧
    (∀ p, ∃ s : Term p →ₗ[ℂ] Term (p+1),
      (∀ x z, s (constGenerator x • z) = constGenerator x • s z) ∧
      (∀ n z, z ∈ termPiece p n → s z ∈ termPiece (p+1) n) ∧
      (∀ z, differential p (s (differential p z)) = differential p z))

/-- The actual relative affine A₁ BGG resolution, constructed without an exactness assumption. -/
def relativeBGGResolution : RelativeBGGResolution.{u,v} where
  differential := TermResolution.differential
  augmentation := TermResolution.augmentation
  square_zero := TermResolution.differential_square_zero
  augmentation_differential := TermResolution.augmentation_differential
  exact_positive := TermResolution.exact_differentials
  exact_zero := TermResolution.exact_differential_augmentation
  augmentation_surjective := TermResolution.augmentation_surjective
  augmentation_equivariant := TermResolution.augmentation_smul
  differential_energy := fun p _ _ h => TermResolution.differential_mem_termPiece p h
  augmentation_energy := fun _ _ h hn => TermResolution.augmentation_eq_zero_of_energy_ne_zero h hn
  relatively_projective := termsRelativelyProjective
  relative_admissible :=
    ⟨⟨TermResolution.constantAugmentationSection,
      TermResolution.augmentation_constantAugmentationSection,
      TermResolution.constantAugmentationSection_constant,
      TermResolution.constantAugmentationSection_mem_energy_zero⟩,
      fun p => ⟨(TermResolution.constantSplitting p).toLinearMap,
        TermResolution.constantSplitting_constant p,
        fun _ _ h => TermResolution.constantSplitting_mem_energy p h,
        TermResolution.differential_constantSplitting_differential p⟩⟩

/-- Existence of the full graded exact relative-projective complex on the stated induced terms. -/
theorem relative_bgg_resolution : Nonempty (RelativeBGGResolution.{u,v}) := ⟨relativeBGGResolution⟩

end KhanSL2.BGG