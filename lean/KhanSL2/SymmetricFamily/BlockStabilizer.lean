module

public import KhanSL2.SymmetricFamily.RootAssignmentTransport
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The explicit first-block stabilizer and its two independent permutation
factors, including their original slot formulas and sign normalization. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

/-- Honest permutations within the first r and last s labelled slots. -/
def blockPermutationHom (r s : ℕ) :
    Equiv.Perm (Fin r) × Equiv.Perm (Fin s) →* Equiv.Perm (Fin (r+s)) :=
  (finSumFinEquiv.permCongrHom).toMonoidHom.comp (Equiv.Perm.sumCongrHom (Fin r) (Fin s))

@[simp] theorem blockPermutation_castAdd (r s : ℕ)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (i : Fin r) :
    blockPermutationHom r s g (Fin.castAdd s i) = Fin.castAdd s (g.1 i) := by
  simp [blockPermutationHom, Equiv.permCongr_apply]

@[simp] theorem blockPermutation_natAdd (r s : ℕ)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (i : Fin s) :
    blockPermutationHom r s g (Fin.natAdd r i) = Fin.natAdd r (g.2 i) := by
  simp [blockPermutationHom, Equiv.permCongr_apply]

/-- The signs multiply without any extra block sign. -/
theorem blockPermutation_sign (r s : ℕ) (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) :
    (blockPermutationHom r s g).sign = g.1.sign * g.2.sign := by
  change (finSumFinEquiv.permCongr (Equiv.sumCongr g.1 g.2)).sign = _
  rw [Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr]

theorem blockPermutationHom_injective (r s : ℕ) : Function.Injective (blockPermutationHom r s) :=
  finSumFinEquiv.permCongrHom.injective.comp Equiv.Perm.sumCongrHom_injective

/-- Each independent block permutation fixes the actual first-block assignment. -/
theorem blockPermutation_firstBlock (r s : ℕ) (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) :
    (blockPermutationHom r s g) • firstBlock r s = firstBlock r s := by
  apply Subtype.ext
  change (Finset.univ.map (Fin.castAddEmb s)).map (blockPermutationHom r s g).toEmbedding =
    Finset.univ.map (Fin.castAddEmb s)
  rw [Finset.map_map]
  have he : (Fin.castAddEmb s).trans (blockPermutationHom r s g).toEmbedding =
      g.1.toEmbedding.trans (Fin.castAddEmb s) := by
    apply Function.Embedding.ext
    intro i
    exact blockPermutation_castAdd r s g i
  rw [he, ← Finset.map_map]
  simp

/-- The original stabilizer of the distinguished assignment. -/
abbrev FirstBlockStabilizer (r s : ℕ) :=
  MulAction.stabilizer (Equiv.Perm (Fin (r+s))) (firstBlock r s)

/-- The independent block permutations, with their proved stabilizer property. -/
def blockStabilizerHom (r s : ℕ) :
    Equiv.Perm (Fin r) × Equiv.Perm (Fin s) →* FirstBlockStabilizer r s where
  toFun g := ⟨blockPermutationHom r s g, blockPermutation_firstBlock r s g⟩
  map_one' := Subtype.ext (blockPermutationHom r s).map_one
  map_mul' g h := Subtype.ext ((blockPermutationHom r s).map_mul g h)

/-- Every actual first-block stabilizer element is a unique independent block permutation. -/
theorem blockStabilizerHom_bijective (r s : ℕ) : Function.Bijective (blockStabilizerHom r s) := by
  constructor
  · intro g h he
    exact blockPermutationHom_injective r s (congrArg Subtype.val he)
  · intro σ
    let τ : Equiv.Perm (Fin r ⊕ Fin s) := finSumFinEquiv.permCongrHom.symm σ.val
    have hm : Set.MapsTo τ (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨i,rfl⟩
      have hfix := σ.property
      change assignmentPermute σ.val (firstBlock r s) = firstBlock r s at hfix
      have hmapped : (Fin.castAdd s i) ∈ (firstBlock r s).val := by
        simp [firstBlock]
      have hmem : σ.val (Fin.castAdd s i) ∈ (firstBlock r s).val := by
        have h : σ.val (Fin.castAdd s i) ∈ (firstBlock r s).val.map σ.val.toEmbedding :=
          Finset.mem_map.mpr ⟨Fin.castAdd s i,hmapped,rfl⟩
        rw [show (firstBlock r s).val.map σ.val.toEmbedding = (firstBlock r s).val from
          congrArg Subtype.val hfix] at h
        exact h
      obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hmem
      refine ⟨j,?_⟩
      change Sum.inl j = finSumFinEquiv.symm (σ.val (finSumFinEquiv (Sum.inl i)))
      rw [finSumFinEquiv_apply_left, ← hj]
      simp
    obtain ⟨g,hg⟩ := Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hm
    refine ⟨g,Subtype.ext ?_⟩
    change finSumFinEquiv.permCongrHom ((Equiv.Perm.sumCongrHom (Fin r) (Fin s)) g) = σ.val
    rw [hg]
    exact finSumFinEquiv.permCongrHom.apply_symm_apply σ.val

/-- Explicit block-group identification with the original first-block stabilizer. -/
def blockStabilizerEquiv (r s : ℕ) :
    Equiv.Perm (Fin r) × Equiv.Perm (Fin s) ≃* FirstBlockStabilizer r s :=
  MulEquiv.ofBijective (blockStabilizerHom r s) (blockStabilizerHom_bijective r s)

/-- The inverse reads the two independent restrictions of a stabilizing permutation. -/
def firstBlockStabilizerEquiv (r s : ℕ) :
    FirstBlockStabilizer r s ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin s) :=
  (blockStabilizerEquiv r s).symm

@[simp] theorem blockStabilizerEquiv_apply (r s : ℕ)
    (g : Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) :
    (blockStabilizerEquiv r s g).val = blockPermutationHom r s g := rfl

/-- The inverse restriction recovers the literal first-block action. -/
theorem firstBlockStabilizer_castAdd (r s : ℕ) (σ : FirstBlockStabilizer r s) (i : Fin r) :
    σ.val (Fin.castAdd s i) = Fin.castAdd s ((firstBlockStabilizerEquiv r s σ).1 i) := by
  have h := congrArg Subtype.val ((blockStabilizerEquiv r s).apply_symm_apply σ)
  change blockPermutationHom r s (firstBlockStabilizerEquiv r s σ) = σ.val at h
  rw [← h, blockPermutation_castAdd]

/-- The inverse restriction recovers the literal last-block action. -/
theorem firstBlockStabilizer_natAdd (r s : ℕ) (σ : FirstBlockStabilizer r s) (i : Fin s) :
    σ.val (Fin.natAdd r i) = Fin.natAdd r ((firstBlockStabilizerEquiv r s σ).2 i) := by
  have h := congrArg Subtype.val ((blockStabilizerEquiv r s).apply_symm_apply σ)
  change blockPermutationHom r s (firstBlockStabilizerEquiv r s σ) = σ.val at h
  rw [← h, blockPermutation_natAdd]

end KhanSL2.SymmetricFamily
