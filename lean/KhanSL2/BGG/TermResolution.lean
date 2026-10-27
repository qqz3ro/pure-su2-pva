module

public import KhanSL2.BGG.HarmonicResolutionDegree
public import KhanSL2.BGG.TermPBWMorphism

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.TermResolution

/-- The specified degreewise differential on the actual relative induced terms.
It is constructed from the proved finite perturbation, not supplied as resolution data. -/
def boundary (p : ℕ) : Term (p+1) →ₗ[PositiveEnveloping] Term p :=
  (termHarmonicProjection p).comp
    (PositiveTransfer.differential.comp (termHarmonicEmbedding (p+1)))

/-- The actual augmented map on the zeroth relative induced term. -/
def augmentation : Term 0 →ₗ[ℂ] ℂ :=
  HarmonicResolution.augmentation.comp ((termHarmonicEmbedding 0).restrictScalars ℂ)

@[simp] theorem augmentation_apply (x : Term 0) :
    augmentation x = HarmonicResolution.augmentation (termHarmonicEmbedding 0 x) := rfl

/-- The induced-term differential is exactly the transferred differential under its identification. -/
theorem embedding_boundary (p : ℕ) (x : Term (p+1)) :
    termHarmonicEmbedding p (boundary p x) =
      PositiveTransfer.differential (termHarmonicEmbedding (p+1) x) :=
  termHarmonicEmbedding_projection_of_mem p _
    (PositiveTransfer.differential_mem_degree (termHarmonicEmbedding_mem (p+1) x))

/-- Every pair of successive specified differentials composes to zero. -/
@[simp] theorem boundary_square_zero (p : ℕ) (x : Term (p+2)) :
    boundary p (boundary (p+1) x) = 0 := by
  apply (show Function.LeftInverse (termHarmonicProjection p) (termHarmonicEmbedding p)
    from termHarmonicProjection_embedding p).injective
  rw [map_zero, embedding_boundary, embedding_boundary, PositiveTransfer.differential_square_zero]

@[simp] theorem augmentation_boundary (x : Term 1) : augmentation (boundary 0 x) = 0 := by
  rw [augmentation_apply, embedding_boundary, HarmonicResolution.augmentation_differential]

/-- Exactness at every positive relative induced term, with no exactness assumption. -/
theorem exact_at_positive_degree (p : ℕ) : Function.Exact (boundary (p+1)) (boundary p) := by
  intro x
  constructor
  · intro hx
    have hc : PositiveTransfer.differential (termHarmonicEmbedding (p+1) x) = 0 := by
      rw [← embedding_boundary p x, hx, map_zero]
    obtain ⟨v, hv, hd⟩ := HarmonicResolution.exactness_positive_degree p
      (termHarmonicEmbedding (p+1) x) (termHarmonicEmbedding_mem (p+1) x) hc
    refine ⟨termHarmonicProjection (p+2) v, ?_⟩
    change termHarmonicProjection (p+1)
      (PositiveTransfer.differential (termHarmonicEmbedding (p+2) (termHarmonicProjection (p+2) v))) = x
    rw [termHarmonicEmbedding_projection_of_mem _ _ hv, hd, termHarmonicProjection_embedding]
  · rintro ⟨y, rfl⟩
    exact boundary_square_zero p y

/-- Exactness at the actual augmented zeroth term. -/
theorem exact_at_zero : Function.Exact (boundary 0) augmentation := by
  intro x
  constructor
  · intro hx
    obtain ⟨v, hv, hd⟩ := HarmonicResolution.augmented_exactness_degree 0
      (termHarmonicEmbedding 0 x) (termHarmonicEmbedding_mem 0 x)
      (PositiveTransfer.differential_eq_zero_of_degree_zero (termHarmonicEmbedding_mem 0 x)) hx
    refine ⟨termHarmonicProjection 1 v, ?_⟩
    change termHarmonicProjection 0
      (PositiveTransfer.differential (termHarmonicEmbedding 1 (termHarmonicProjection 1 v))) = x
    rw [termHarmonicEmbedding_projection_of_mem _ _ hv, hd, termHarmonicProjection_embedding]
  · rintro ⟨y, rfl⟩
    exact augmentation_boundary y

/-- The augmentation of the degreewise resolution is surjective. -/
theorem augmentation_surjective : Function.Surjective augmentation := by
  intro r
  refine ⟨termHarmonicProjection 0 (HarmonicResolution.scalarSection r), ?_⟩
  rw [augmentation_apply, termHarmonicEmbedding_projection_of_mem _ _
    (HarmonicResolution.scalarSection_mem_degree_zero r), HarmonicResolution.augmentation_scalarSection]

/-- All degrees of the constructed augmented complex are exact on the prescribed
relative induced terms. Full-current equivariance and energy preservation are separate properties. -/
theorem exact_augmented_complex :
    (∀ p, Function.Exact (boundary (p+1)) (boundary p)) ∧
    Function.Exact (boundary 0) augmentation ∧ Function.Surjective augmentation :=
  ⟨exact_at_positive_degree, exact_at_zero, augmentation_surjective⟩

end KhanSL2.BGG.TermResolution