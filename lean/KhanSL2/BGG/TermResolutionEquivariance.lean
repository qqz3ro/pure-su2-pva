module

public import KhanSL2.BGG.TermResolution
public import KhanSL2.BGG.HarmonicTensorEquivariance
public import KhanSL2.BGG.PositiveTransferEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.TermResolution

/-- Each degreewise boundary intertwines the actual constant-current action. -/
theorem boundary_constant (p : ℕ) (x : G) (v : Term (p+1)) :
    boundary p (constGenerator x • v) = constGenerator x • boundary p v := by
  change termHarmonicProjection p
    (PositiveTransfer.differential (termHarmonicEmbedding (p+1) (constGenerator x • v))) = _
  rw [termHarmonicEmbedding_constant, PositiveTransfer.differential_constantAction,
    termHarmonicProjection_constant]
  rfl

/-- The constructed relative BGG differential is a morphism for the full current algebra. -/
def differential (p : ℕ) : Term (p+1) →ₗ[Enveloping] Term p :=
  termMapOfPositiveConstant ((boundary p).restrictScalars ℂ)
    (fun u v => (boundary p).map_smul u v) (boundary_constant p)

@[simp] theorem differential_apply (p : ℕ) (v : Term (p+1)) : differential p v = boundary p v := rfl

@[simp] theorem differential_square_zero (p : ℕ) (v : Term (p+2)) :
    differential p (differential (p+1) v) = 0 := boundary_square_zero p v

@[simp] theorem augmentation_differential (v : Term 1) : augmentation (differential 0 v) = 0 :=
  augmentation_boundary v

/-- Exactness in all positive degrees for the full current-module maps. -/
theorem exact_differentials (p : ℕ) :
    Function.Exact (differential (p+1)) (differential p) := exact_at_positive_degree p

/-- Exactness at the augmentation for the full current-module differential. -/
theorem exact_differential_augmentation : Function.Exact (differential 0) augmentation := exact_at_zero

/-- The all-degree augmented complex on the requested relative induced modules is exact,
and its differentials are actual full current-enveloping module morphisms. -/
theorem exact_current_module_complex :
    (∀ p, Function.Exact (differential (p+1)) (differential p)) ∧
    Function.Exact (differential 0) augmentation ∧ Function.Surjective augmentation :=
  ⟨exact_differentials, exact_differential_augmentation, augmentation_surjective⟩

end KhanSL2.BGG.TermResolution