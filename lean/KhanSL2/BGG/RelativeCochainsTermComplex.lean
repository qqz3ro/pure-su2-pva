module

public import KhanSL2.BGG.RelativeCochainsInduced
public import KhanSL2.BGG.TermResolutionEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Compatibility with the specified differentials on the actual induced BGG terms. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

@[simp] theorem harmonicCoefficientEquiv_apply (p : ℕ) (f : harmonicDegree M p)
    (v : Coefficient p) :
    (harmonicCoefficientEquiv M p f).val v =
      f.val.val (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p v) := rfl

@[simp] theorem harmonicInducedEquiv_generator (p : ℕ) (f : harmonicDegree M p)
    (v : Coefficient p) :
    harmonicInducedEquiv M p f (termGenerator p v) =
      f.val.val (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p v) := by
  have h := congrArg (fun g : coefficientHom M (Coefficient p) => g.val v)
    ((inducedCoefficientEquiv M p).apply_symm_apply (harmonicCoefficientEquiv M p f))
  change harmonicInducedEquiv M p f (termGenerator p v) =
    (harmonicCoefficientEquiv M p f).val v at h
  exact h

set_option maxHeartbeats 800000 in
/-- The coefficient identification is exactly precomposition by the actual term embedding. -/
theorem harmonicInducedEquiv_apply (p : ℕ) (f : harmonicDegree M p) (t : Term p) :
    harmonicInducedEquiv M p f t = f.val.val (termHarmonicEmbedding p t) := by
  let F := harmonicInducedEquiv M p f
  let g := f.val.val
  let E := positiveTensorModuleEquivTerm p
  have hgen (w : Coefficient p) : F (termGenerator p w) =
      g (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p w) :=
    harmonicInducedEquiv_generator M p f w
  have h (v : PositiveEnveloping ⊗[ℂ] Coefficient p) :
      F (E v) = g (termHarmonicEmbedding p (E v)) := by
    induction v using TensorProduct.inductionOn with
    | tmul a w =>
      have he : E (a ⊗ₜ[ℂ] w) = positiveFactor a • termGenerator p w :=
        positiveTensorEquivTerm_tmul p a w
      have ht : termHarmonicEmbedding p (E (a ⊗ₜ[ℂ] w)) =
          a ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p w :=
        (termHarmonicEmbedding_equiv p (a ⊗ₜ[ℂ] w)).trans (harmonicTensorEmbedding_tmul p a w)
      calc
        F (E (a ⊗ₜ[ℂ] w)) = F (positiveFactor a • termGenerator p w) := congrArg F he
        _ = positiveFactor a • F (termGenerator p w) := F.map_smul _ _
        _ = positiveFactor a • g (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p w) :=
          congrArg (fun z : M => positiveFactor a • z) (hgen w)
        _ = g (a ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p w) := by
          change a • g (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p w) = _
          simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
            (g.map_smul a (1 ⊗ₜ[ℂ] PositiveCE.standardHarmonicEmbedding p w)).symm
        _ = g (termHarmonicEmbedding p (E (a ⊗ₜ[ℂ] w))) := congrArg g ht.symm
    | add v w hv hw => simp only [map_add, hv, hw]
  exact (congrArg F (E.apply_symm_apply t).symm).trans
    ((h (E.symm t)).trans (congrArg (fun z => g (termHarmonicEmbedding p z)) (E.apply_symm_apply t)))
/-- The actual degreewise differential on homogeneous harmonic cochains. -/
def harmonicDegreeDifferential (p : ℕ) : harmonicDegree M p →ₗ[ℂ] harmonicDegree M (p+1) :=
  ((harmonicDifferential M).comp (harmonicDegree M p).subtype).codRestrict
    (harmonicDegree M (p+1)) (fun f => harmonicDifferential_mem_harmonicDegree M f.property)

@[simp] theorem harmonicDegreeDifferential_apply (p : ℕ) (f : harmonicDegree M p)
    (t : HarmonicTensor) :
    (harmonicDegreeDifferential M p f).val.val t = f.val.val (PositiveTransfer.differential t) := rfl

/-- Cochains on the specified induced terms, with the specified full-current-linear differential. -/
def termDifferential (p : ℕ) : (Term p →ₗ[Enveloping] M) →ₗ[ℂ] (Term (p+1) →ₗ[Enveloping] M) where
  toFun f := f.comp (TermResolution.differential p)
  map_add' f g := by apply LinearMap.ext; intro t; rfl
  map_smul' r f := by apply LinearMap.ext; intro t; rfl

@[simp] theorem termDifferential_apply (p : ℕ) (f : Term p →ₗ[Enveloping] M) (t : Term (p+1)) :
    termDifferential M p f t = f (TermResolution.differential p t) := rfl

@[simp] theorem termDifferential_square_zero (p : ℕ) (f : Term p →ₗ[Enveloping] M) :
    termDifferential M (p+1) (termDifferential M p f) = 0 := by
  apply LinearMap.ext
  intro t
  simp only [termDifferential_apply, TermResolution.differential_square_zero,
    map_zero, LinearMap.zero_apply]

set_option maxHeartbeats 800000 in
/-- The homogeneous comparison intertwines the actual BGG and harmonic cochain differentials. -/
theorem harmonicInducedEquiv_differential (p : ℕ) (f : harmonicDegree M p) :
    harmonicInducedEquiv M (p+1) (harmonicDegreeDifferential M p f) =
      termDifferential M p (harmonicInducedEquiv M p f) := by
  apply LinearMap.ext
  intro t
  calc
    _ = (harmonicDegreeDifferential M p f).val.val (termHarmonicEmbedding (p+1) t) :=
      harmonicInducedEquiv_apply M (p+1) (harmonicDegreeDifferential M p f) t
    _ = f.val.val (PositiveTransfer.differential (termHarmonicEmbedding (p+1) t)) := rfl
    _ = f.val.val (termHarmonicEmbedding p (TermResolution.differential p t)) :=
      congrArg f.val.val (TermResolution.embedding_boundary p t).symm
    _ = harmonicInducedEquiv M p f (TermResolution.differential p t) :=
      (harmonicInducedEquiv_apply M p f (TermResolution.differential p t)).symm
    _ = _ := rfl
end KhanSL2.BGG.RelativeCochains
