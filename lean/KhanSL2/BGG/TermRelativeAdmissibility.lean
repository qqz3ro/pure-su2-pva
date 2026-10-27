module

public import KhanSL2.BGG.TermEnergyLie
public import KhanSL2.BGG.FiniteSl2Splitting

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
noncomputable section
open scoped DirectSum
namespace KhanSL2.BGG.TermResolution
local instance termConstantLieRingModule (p : ℕ) : LieRingModule G (Term p) :=
  RelativeCochains.constantLieRingModule (Term p)
local instance termConstantLieModule (p : ℕ) : LieModule ℂ G (Term p) :=
  RelativeCochains.constantLieModule (Term p)

/-- Choose an actual equivariant generalized inverse on each finite energy component. -/
def energySplitting (p : ℕ) (n : ℤ) : energyLiePiece p n →ₗ⁅ℂ,G⁆ energyLiePiece (p+1) n :=
  Classical.choose (exists_lie_generalizedInverse (energyLieDifferential p n))

theorem energySplitting_spec (p : ℕ) (n : ℤ) (u : energyLiePiece (p+1) n) :
    energyLieDifferential p n (energySplitting p n (energyLieDifferential p n u)) =
      energyLieDifferential p n u :=
  Classical.choose_spec (exists_lie_generalizedInverse (energyLieDifferential p n)) u

/-- The componentwise map on the actual external energy direct sums. -/
def energySumSplitting (p : ℕ) :=
  DirectSum.lieModuleMap (R := ℂ) (L := G)
    (P := fun n : ℤ => (energyLiePiece p n : Type))
    (Q := fun n : ℤ => (energyLiePiece (p+1) n : Type)) (energySplitting p)
/-- Assemble the finite-energy splittings on the genuine algebraic direct sum. -/
def constantSplitting (p : ℕ) : Term p →ₗ⁅ℂ,G⁆ Term (p+1) :=
  (energyLieEquiv (p+1)).toLieModuleHom.comp
    ((energySumSplitting p).comp (energyLieEquiv p).symm.toLieModuleHom)
@[simp] theorem constantSplitting_coe (p : ℕ) (n : ℤ) (u : energyLiePiece p n) :
    constantSplitting p (u : Term p) = (energySplitting p n u : Term (p+1)) := by
  let E := fun q : ℕ => DirectSum ℤ (fun k => ↥(energyLiePiece q k))
  have he : (energySumSplitting p).toLinearMap =
      DirectSum.lmap (fun k => (energySplitting p k).toLinearMap) :=
    DirectSum.lieModuleMap_toLinearMap (energySplitting p)
  have hm : energySumSplitting p (DirectSum.of (fun k => energyLiePiece p k) n u) =
      DirectSum.of (fun k => energyLiePiece (p+1) k) n (energySplitting p n u) :=
    (congrArg (fun f : E p →ₗ[ℂ] E (p+1) =>
      f (DirectSum.of (fun k => energyLiePiece p k) n u)) he).trans
      (DirectSum.lmap_of (fun k => (energySplitting p k).toLinearMap) n u)
  calc
    constantSplitting p u = energyLieEquiv (p+1)
        (energySumSplitting p ((energyLieEquiv p).symm u)) := rfl
    _ = energyLieEquiv (p+1)
        (energySumSplitting p (DirectSum.of (fun k => energyLiePiece p k) n u)) :=
      congrArg (fun z : E p => energyLieEquiv (p+1) (energySumSplitting p z))
        (energyLieEquiv_symm_coe p n u)
    _ = energyLieEquiv (p+1)
        (DirectSum.of (fun k => energyLiePiece (p+1) k) n (energySplitting p n u)) :=
      congrArg (energyLieEquiv (p+1)) hm
    _ = (energySplitting p n u : Term (p+1)) := energyLieEquiv_of (p+1) n _
/-- These actual splittings preserve energy. -/
theorem constantSplitting_mem_energy (p : ℕ) {n : ℤ} {u : Term p}
    (hu : u ∈ termPiece p n) : constantSplitting p u ∈ termPiece (p+1) n := by
  change constantSplitting p ((⟨u, hu⟩ : energyLiePiece p n) : Term p) ∈ termPiece (p+1) n
  rw [constantSplitting_coe]
  exact (energySplitting p n ⟨u, hu⟩).property

/-- The assembled splitting is a right inverse on the actual image of every differential. -/
theorem differential_constantSplitting_differential (p : ℕ) (u : Term (p+1)) :
    differential p (constantSplitting p (differential p u)) = differential p u := by
  have hu : u ∈ ⨆ n, termPiece (p+1) n := by rw [iSup_termPiece_eq_top]; trivial
  induction hu using Submodule.iSup_induction' with
  | mem n u hu =>
    change differential p (constantSplitting p
      (energyLieDifferential p n (⟨u, hu⟩ : energyLiePiece (p+1) n) : Term p)) = _
    rw [constantSplitting_coe]
    exact congrArg (fun z : energyLiePiece p n => (z : Term p))
      (energySplitting_spec p n ⟨u, hu⟩)
  | zero => simp
  | add u v _ _ hu hv => simp only [map_add, hu, hv]

/-- Equivariance is for the actual constant action inherited from U(sl₂[z]). -/
theorem constantSplitting_constant (p : ℕ) (x : G) (u : Term p) :
    constantSplitting p (constGenerator x • u) = constGenerator x • constantSplitting p u :=
  (constantSplitting p).map_lie x u

/-- Exactness turns the splitting on images into a section over every positive cycle. -/
theorem differential_constantSplitting_cycle (p : ℕ) (u : Term (p+1))
    (hu : differential p u = 0) : differential (p+1) (constantSplitting (p+1) u) = u := by
  obtain ⟨v, rfl⟩ := (exact_differentials p u).mp hu
  exact differential_constantSplitting_differential (p+1) v

/-- The degree-zero augmentation kernel is split in the same actual constant representation. -/
theorem differential_constantSplitting_augmentation_kernel (u : Term 0)
    (hu : augmentation u = 0) : differential 0 (constantSplitting 0 u) = u := by
  obtain ⟨v, rfl⟩ := (exact_differential_augmentation u).mp hu
  exact differential_constantSplitting_differential 0 v

instance finiteDimensional_trivialScalar : FiniteDimensional ℂ (TrivialLieModule ℂ G ℂ) :=
  FiniteDimensional.of_injective (K := ℂ) (V := TrivialLieModule ℂ G ℂ) (V₂ := ℂ)
    (TrivialLieModule.equiv ℂ G ℂ).toLinearMap
    (TrivialLieModule.equiv ℂ G ℂ).injective

/-- The finite energy-zero augmentation has an actual equivariant generalized inverse. -/
def energyAugmentationSplitting : TrivialLieModule ℂ G ℂ →ₗ⁅ℂ,G⁆ energyLiePiece 0 0 :=
  Classical.choose (exists_lie_generalizedInverse energyLieAugmentation)

theorem energyAugmentationSplitting_spec (r : TrivialLieModule ℂ G ℂ) :
    energyLieAugmentation (energyAugmentationSplitting r) = r := by
  obtain ⟨u, rfl⟩ := energyLieAugmentation_surjective r
  exact Classical.choose_spec (exists_lie_generalizedInverse energyLieAugmentation) u

/-- The augmented scalar module has a constant-equivariant section in energy zero. -/
def constantAugmentationSection : ℂ →ₗ[ℂ] Term 0 :=
  ((energyLiePiece 0 0).incl.toLinearMap.comp energyAugmentationSplitting.toLinearMap).comp
    (TrivialLieModule.equiv ℂ G ℂ).symm.toLinearMap

@[simp] theorem augmentation_constantAugmentationSection (r : ℂ) :
    augmentation (constantAugmentationSection r) = r := by
  apply (TrivialLieModule.equiv ℂ G ℂ).symm.injective
  exact energyAugmentationSplitting_spec ((TrivialLieModule.equiv ℂ G ℂ).symm r)

theorem constantAugmentationSection_constant (x : G) (r : ℂ) :
    constGenerator x • constantAugmentationSection r = 0 := by
  have h := energyAugmentationSplitting.map_lie x ((TrivialLieModule.equiv ℂ G ℂ).symm r)
  change energyAugmentationSplitting 0 = _ at h
  rw [map_zero] at h
  exact congrArg (fun z : energyLiePiece 0 0 => (z : Term 0)) h.symm

theorem constantAugmentationSection_mem_energy_zero (r : ℂ) :
    constantAugmentationSection r ∈ termPiece 0 0 :=
  (energyAugmentationSplitting ((TrivialLieModule.equiv ℂ G ℂ).symm r)).property

/-- Actual constant-equivariant splittings make the entire augmented exact complex
admissible for relative homological algebra. No splitting is assumed. -/
theorem relative_admissibility :
    (∃ s : ℂ →ₗ[ℂ] Term 0, (∀ r, augmentation (s r) = r) ∧
      (∀ x r, constGenerator x • s r = 0)) ∧
    (∀ p, ∃ s : Term p →ₗ[ℂ] Term (p+1),
      (∀ x u, s (constGenerator x • u) = constGenerator x • s u) ∧
      (∀ u, differential p (s (differential p u)) = differential p u)) :=
  ⟨⟨constantAugmentationSection, augmentation_constantAugmentationSection,
      constantAugmentationSection_constant⟩,
    fun p => ⟨(constantSplitting p).toLinearMap, constantSplitting_constant p,
      differential_constantSplitting_differential p⟩⟩

end KhanSL2.BGG.TermResolution
