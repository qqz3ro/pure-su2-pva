module

public import KhanSL2.Factorization.WeightedRootModel
public import KhanSL2.Factorization.OrbitStabilizerTwist

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.WeightedRootModel
open MvPolynomial PolynomialBGG

abbrev BlockGroup (q r : ℕ) := Equiv.Perm (Fin q) × Equiv.Perm (Fin r)

def blockPermutation {q r : ℕ} (g : BlockGroup q r) : Equiv.Perm (Fin q ⊕ Fin r) :=
  Equiv.sumCongr g.1 g.2

def repeatedPermutation {q r : ℕ} (g : BlockGroup q r) : Equiv.Perm (Fin (q+2*r)) :=
  (rootIndexEquiv q r).symm.trans
    ((Equiv.sumCongr g.1 (Equiv.prodCongr (Equiv.refl (Fin 2)) g.2)).trans
      (rootIndexEquiv q r))

theorem weightedRootIndex_permutation {q r : ℕ} (g : BlockGroup q r) (i : Fin (q+2*r)) :
    weightedRootIndex q r (repeatedPermutation g i) = blockPermutation g (weightedRootIndex q r i) := by
  obtain ⟨a,rfl⟩ := (rootIndexEquiv q r).surjective i
  cases a with
  | inl a => simp [repeatedPermutation,weightedRootIndex,rootProjection,blockPermutation]
  | inr a => simp [repeatedPermutation,weightedRootIndex,rootProjection,blockPermutation]

/-- Permutations inside each weight class fix the prescribed coefficient map. -/
theorem rename_weightedRootMap {q r : ℕ} (g : BlockGroup q r) (a : Depth.RB (q+2*r)) :
    rename (blockPermutation g) (show MvPolynomial (Fin q ⊕ Fin r) ℂ from weightedRootMap q r a) =
      weightedRootMap q r a := by
  change rename (blockPermutation g) (rename (weightedRootIndex q r)
    (Modules.elementaryAlgEquiv (q+2*r) a).val) = _
  rw [rename_rename]
  have he : (blockPermutation g : (Fin q ⊕ Fin r) → Fin q ⊕ Fin r) ∘ weightedRootIndex q r =
      weightedRootIndex q r ∘ (repeatedPermutation g : Fin (q+2*r) → Fin (q+2*r)) := by
    funext i
    exact (weightedRootIndex_permutation g i).symm
  rw [he,← rename_rename,(Modules.elementaryAlgEquiv (q+2*r) a).property (repeatedPermutation g)]
  rfl

/-- The actual block permutations act by coefficient-algebra automorphisms. -/
def blockRootAutomorphism {q r : ℕ} (g : BlockGroup q r) :
    LabelledWeightedRing q r ≃ₐ[Depth.RB (q+2*r)] LabelledWeightedRing q r where
  __ := (renameEquiv ℂ (blockPermutation g)).toRingEquiv
  commutes' a := rename_weightedRootMap g a

@[simp] theorem blockRootAutomorphism_apply {q r : ℕ} (g : BlockGroup q r)
    (p : LabelledWeightedRing q r) :
    blockRootAutomorphism g p = rename (blockPermutation g)
      (show MvPolynomial (Fin q ⊕ Fin r) ℂ from p) := rfl

/-- The actual algebra action, bundled for orbit/stabilizer descent. -/
def blockRootAction (q r : ℕ) :
    BlockGroup q r →* (LabelledWeightedRing q r ≃ₐ[Depth.RB (q+2*r)] LabelledWeightedRing q r) where
  toFun := blockRootAutomorphism
  map_one' := by
    apply AlgEquiv.ext
    intro p
    change rename (blockPermutation (1 : BlockGroup q r)) p = p
    have he : (blockPermutation (1 : BlockGroup q r) : (Fin q ⊕ Fin r) → Fin q ⊕ Fin r) = id := by
      funext i
      cases i <;> rfl
    rw [he]
    exact rename_id_apply p
  map_mul' g h := by
    apply AlgEquiv.ext
    intro p
    change rename (blockPermutation (g*h)) p = rename (blockPermutation g) (rename (blockPermutation h) p)
    rw [rename_rename]
    have he : (blockPermutation (g*h) : (Fin q ⊕ Fin r) → Fin q ⊕ Fin r) =
        (blockPermutation g : (Fin q ⊕ Fin r) → Fin q ⊕ Fin r) ∘ blockPermutation h := by
      funext i
      cases i <;> rfl
    rw [he]

/-- The scalar character is the sign on the odd roots, trivial on the even roots. -/
def blockSign (q r : ℕ) : BlockGroup q r →* (Depth.RB (q+2*r))ˣ :=
  (Units.map (Int.castRingHom (Depth.RB (q+2*r)))).comp
    (Equiv.Perm.sign.comp (MonoidHom.fst _ _))

/-- Signed coefficient-linear permutation of the actual labelled polynomial module. -/
def signedBlockOperator {q r : ℕ} (g : BlockGroup q r) :
    Module.End (Depth.RB (q+2*r)) (LabelledWeightedRing q r) :=
  ((blockRootAutomorphism g).toLinearEquiv.trans (LinearEquiv.smulOfUnit (blockSign q r g))).toLinearMap

/-- The signed-invariant module with the original weighted coefficient action. -/
def signedInvariantModule (q r : ℕ) : Submodule (Depth.RB (q+2*r)) (LabelledWeightedRing q r) where
  carrier := {p | ∀ g : BlockGroup q r, signedBlockOperator g p = p}
  zero_mem' := by simp
  add_mem' hp hq g := by rw [map_add,hp g,hq g]
  smul_mem' c _ hp g := by rw [map_smul,hp g]

/-- Forgetting the coefficient action gives the same polynomial subtype. -/
abbrev signedInvariantComplexModule (q r : ℕ) : Submodule ℂ (LabelledWeightedRing q r) :=
  (signedInvariantModule q r).restrictScalars ℂ

@[simp] theorem signedInvariant_smul_val (q r : ℕ) (a : Depth.RB (q+2*r))
    (p : signedInvariantModule q r) :
    (a • p : signedInvariantModule q r).val = weightedRootMap q r a * p.val := rfl

end KhanSL2.Factorization.WeightedRootModel

