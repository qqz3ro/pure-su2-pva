module

public import KhanSL2.SymmetricFamily.LocalTopQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-! The induced finite current filtration on the kernel of the actual top
quotient, with faithful maps of its graded pieces to the original graded pieces. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization.EvenWeightBounds

/-- A genuine current map induces a current map of the actual compatible quotients. -/
def currentQuotientMap {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
    (P : LieSubmodule ℂ BGG.Current M) (Q : LieSubmodule ℂ BGG.Current N)
    (f : M →ₗ⁅ℂ,BGG.Current⁆ N) (hf : P ≤ Q.comap f) :
    (M ⧸ P) →ₗ⁅ℂ,BGG.Current⁆ (N ⧸ Q) where
  toLinearMap := P.toSubmodule.mapQ Q.toSubmodule f.toLinearMap hf
  map_lie' {x v} := by
    obtain ⟨v,rfl⟩ := LieSubmodule.Quotient.surjective_mk' P v
    exact congrArg (LieSubmodule.Quotient.mk' Q) (f.map_lie x v)

/-- The induced quotient map is injective when the source relation is the precise preimage. -/
theorem currentQuotientMap_injective {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    [AddCommGroup N] [Module ℂ N] [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
    (P : LieSubmodule ℂ BGG.Current M) (Q : LieSubmodule ℂ BGG.Current N)
    (f : M →ₗ⁅ℂ,BGG.Current⁆ N) (hf : P ≤ Q.comap f) (he : Q.comap f = P) :
    Function.Injective (currentQuotientMap P Q f hf) := by
  apply LinearMap.ker_eq_bot.mp
  change LinearMap.ker (P.toSubmodule.mapQ Q.toSubmodule f.toLinearMap hf) = ⊥
  rw [Submodule.ker_mapQ,show Q.toSubmodule.comap f.toLinearMap = P.toSubmodule from
    congrArg LieSubmodule.toSubmodule he,Submodule.mkQ_map_self]

/-- The actual invariant kernel of the top evaluation quotient. -/
abbrev LocalTopKernel (k : ℕ) (a : ℂ) := (localSymmetricTopQuotient k a).ker

/-- The original displacement filtration pulled back to the actual kernel. -/
def localTopKernelFiltration (k : ℕ) (a : ℂ) (d : ℕ) :
    LieSubmodule ℂ BGG.Current (LocalTopKernel k a) :=
  (localSymmetricFiltration k a d).comap (LocalTopKernel k a).incl

@[simp] theorem localTopKernelFiltration_zero (k : ℕ) (a : ℂ) :
    localTopKernelFiltration k a 0 = ⊤ := by
  ext v
  change v.val ∈ localSymmetricFiltration k a 0 ↔ _
  rw [localSymmetricFiltration_zero]
  rfl

theorem localTopKernelFiltration_antitone (k : ℕ) (a : ℂ) :
    Antitone (localTopKernelFiltration k a) := by
  intro d e h v hv
  exact localSymmetricFiltration_antitone k a h hv

theorem localTopKernelFiltration_terminates (k : ℕ) (a : ℂ) :
    ∃ d, localTopKernelFiltration k a d = ⊥ := by
  obtain ⟨d,hd⟩ := localSymmetricFiltration_terminates k a
  refine ⟨d,le_antisymm ?_ bot_le⟩
  intro v hv
  have hv' : v.val ∈ localSymmetricFiltration k a d := hv
  rw [hd] at hv'
  change v = 0
  exact Subtype.ext hv'

/-- Each kernel filtration term includes in the corresponding original term. -/
def localTopKernelFiltrationInclusion (k : ℕ) (a : ℂ) (d : ℕ) :
    localTopKernelFiltration k a d →ₗ⁅ℂ,BGG.Current⁆ localSymmetricFiltration k a d where
  toLinearMap :=
    { toFun := fun v => ⟨v.val.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_lie' := fun {_ _} => rfl

/-- The successive relation submodule of the actual kernel filtration. -/
def localTopKernelSuccessor (k : ℕ) (a : ℂ) (d : ℕ) :
    LieSubmodule ℂ BGG.Current (localTopKernelFiltration k a d) :=
  (localTopKernelFiltration k a (d+1)).comap (localTopKernelFiltration k a d).incl

abbrev LocalTopKernelGraded (k : ℕ) (a : ℂ) (d : ℕ) :=
  localTopKernelFiltration k a d ⧸ localTopKernelSuccessor k a d

/-- The actual graded inclusion, before any decomposition into irreducibles. -/
def localTopKernelGradedMap (k : ℕ) (a : ℂ) (d : ℕ) :
    LocalTopKernelGraded k a d →ₗ⁅ℂ,BGG.Current⁆ LocalSymmetricGraded k a d :=
  currentQuotientMap (localTopKernelSuccessor k a d) (localSymmetricSuccessor k a d)
    (localTopKernelFiltrationInclusion k a d) (fun _ h => h)

theorem localTopKernelGradedMap_injective (k : ℕ) (a : ℂ) (d : ℕ) :
    Function.Injective (localTopKernelGradedMap k a d) :=
  currentQuotientMap_injective _ _ _ _ rfl

/-- Every kernel graded piece has the original support-point evaluation action. -/
theorem localTopKernelGraded_mode (k : ℕ) (a : ℂ) (d n : ℕ) (x : BGG.G)
    (v : LocalTopKernelGraded k a d) : ⁅BGG.mode n x,v⁆ = a^n • ⁅BGG.constant x,v⁆ := by
  apply localTopKernelGradedMap_injective k a d
  rw [LieModuleHom.map_lie,map_smul,LieModuleHom.map_lie]
  exact localSymmetricGraded_mode k a d n x _

/-- The degree-zero kernel graded image is killed by the actual top quotient. -/
theorem localTopKernelGradedMap_zero_killed (k : ℕ) (a : ℂ) (v : LocalTopKernelGraded k a 0) :
    localSymmetricGradedTopQuotient k a (localTopKernelGradedMap k a 0 v) = 0 := by
  obtain ⟨v,rfl⟩ := LieSubmodule.Quotient.surjective_mk' (localTopKernelSuccessor k a 0) v
  exact v.val.property

end KhanSL2.SymmetricFamily
