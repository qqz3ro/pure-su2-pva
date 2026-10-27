module

public import KhanSL2.Factorization.WeightedRootModelAction
public import KhanSL2.Factorization.OrbitStabilizerAverage

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel

/-- The signed permutations form an honest representation over the original coefficient ring. -/
def signedBlockAction (q r : ℕ) :
    BlockGroup q r →* Module.End (Depth.RB (q+2*r)) (LabelledWeightedRing q r) where
  toFun := signedBlockOperator
  map_one' := by
    apply LinearMap.ext
    intro p
    change (blockSign q r 1 : Depth.RB (q+2*r)) • blockRootAutomorphism 1 p = p
    have h : blockRootAutomorphism (1 : BlockGroup q r) p = p :=
      congrArg (fun e => e p) (blockRootAction q r).map_one
    rw [map_one,Units.val_one,one_smul,h]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    change (blockSign q r (g*h) : Depth.RB (q+2*r)) • blockRootAutomorphism (g*h) p =
      (blockSign q r g : Depth.RB (q+2*r)) • blockRootAutomorphism g
        ((blockSign q r h : Depth.RB (q+2*r)) • blockRootAutomorphism h p)
    have hm : blockRootAutomorphism (g*h) p = blockRootAutomorphism g (blockRootAutomorphism h p) :=
      congrArg (fun e => e p) ((blockRootAction q r).map_mul g h)
    rw [map_mul,Units.val_mul,hm,map_smul,smul_smul]

def blockNormalization (q r : ℕ) : Depth.RB (q+2*r) :=
  algebraMap ℂ (Depth.RB (q+2*r)) ((Fintype.card (BlockGroup q r) : ℂ)⁻¹)

theorem blockNormalization_mul_card (q r : ℕ) :
    blockNormalization q r * (Fintype.card (BlockGroup q r) : Depth.RB (q+2*r)) = 1 := by
  have hn : (Fintype.card (BlockGroup q r) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold blockNormalization
  rw [← map_natCast (algebraMap ℂ (Depth.RB (q+2*r))),← map_mul,inv_mul_cancel₀ hn,map_one]

/-- Signed polynomial invariants commute with every coefficient specialization. -/
def signedInvariantBaseChangeEquiv (q r : ℕ) (A : Type*) [CommRing A]
    [Algebra (Depth.RB (q+2*r)) A] :
    A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r ≃ₗ[A]
      SymmetricFamily.fixedOperators (fun g : BlockGroup q r => (signedBlockOperator g).baseChange A) :=
  FiberTransport.fixedVectorsBaseChangeEquiv A (signedBlockAction q r)
    (blockNormalization q r) (blockNormalization_mul_card q r)

@[simp] theorem signedInvariantBaseChangeEquiv_apply (q r : ℕ) (A : Type*) [CommRing A]
    [Algebra (Depth.RB (q+2*r)) A]
    (x : A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) :
    (signedInvariantBaseChangeEquiv q r A x).val =
      (signedInvariantModule q r).subtype.baseChange A x := rfl

end KhanSL2.Factorization.WeightedRootModel
