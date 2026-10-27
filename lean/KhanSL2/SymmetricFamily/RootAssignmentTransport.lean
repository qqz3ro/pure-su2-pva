module

public import KhanSL2.SymmetricFamily.RootPermutation
public import KhanSL2.SymmetricFamily.RootUniversal
public import KhanSL2.Factorization.OrbitStabilizerQuotient

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Coherent transport of the actual root-assignment quotient algebras. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization Factorization.WeightedRoots

/-- The honest relabelling action on assignments. -/
instance assignmentMulAction (k r : ℕ) : MulAction (Equiv.Perm (Fin k)) (Assignment k r) where
  smul := assignmentPermute
  one_smul S := by
    apply Subtype.ext
    exact Finset.map_refl (s := S.val)
  mul_smul σ τ S := by
    apply Subtype.ext
    change S.val.map (σ*τ).toEmbedding = (S.val.map τ.toEmbedding).map σ.toEmbedding
    rw [Finset.map_map]
    rfl

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- The original labelled-root permutations as a genuine algebraic group action. -/
def baseRootPermutationRepresentation :
    Equiv.Perm (Fin k) →* (RootBase k A ≃ₐ[A] RootBase k A) where
  toFun := baseRootPermutation k A
  map_one' := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply rootBaseAlgHom_ext
    intro i
    change baseRootPermutation k A 1 (baseRoot k A i) = baseRoot k A i
    rw [baseRootPermutation_baseRoot]
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply rootBaseAlgHom_ext
    intro i
    change baseRootPermutation k A (σ*τ) (baseRoot k A i) =
      baseRootPermutation k A σ (baseRootPermutation k A τ (baseRoot k A i))
    rw [baseRootPermutation_baseRoot, baseRootPermutation_baseRoot, baseRootPermutation_baseRoot]
    rfl

/-- The actual factor-identity ideal attached to a root assignment. -/
abbrev assignmentFactorIdeal {r s : ℕ} (c : Collision.ChartData k r s A)
    (S : Assignment k r) : Ideal (RootBase k A) :=
  factorIdeal (c.f₁.map (algebraMap A (RootBase k A)))
    (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1) S.val

/-- The quotient transport preserves the original chart scalars and actual factor ideals. -/
def rootAssignmentTransport {r s : ℕ} (c : Collision.ChartData k r s A) :
    FiberTransport (R := A) (G := Equiv.Perm (Fin k))
      (fun S : Assignment k r => RootBase k A ⧸ assignmentFactorIdeal k A c S) :=
  FiberTransport.quotients (baseRootPermutationRepresentation k A)
    (assignmentFactorIdeal k A c) (fun σ S => baseRootPermutation_factorIdeal k A c σ S.val)

end KhanSL2.SymmetricFamily
