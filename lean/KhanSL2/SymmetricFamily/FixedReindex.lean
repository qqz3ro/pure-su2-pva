module

public import KhanSL2.SymmetricFamily.AverageBaseChange
public import KhanSL2.Factorization.OrbitStabilizerDecomposition

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Reindexing the specified fixed-operator equations does not change their
actual invariant submodule or its scalar action. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

/-- Reindex the actual fixed equations through an explicit equivalence of indices. -/
def fixedReindexEquiv {R M I J : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ρ : I → Module.End R M) (τ : J → Module.End R M) (e : I ≃ J)
    (he : ∀ i, τ (e i) = ρ i) :
    fixedOperators ρ ≃ₗ[R] Factorization.FiberTransport.fixedVectors τ where
  toFun x := ⟨x.val,fun j => by
    have h := he (e.symm j)
    rw [e.apply_symm_apply j] at h
    rw [h]
    exact x.property (e.symm j)⟩
  invFun x := ⟨x.val,fun i => by rw [← he i]; exact x.property (e i)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KhanSL2.SymmetricFamily
