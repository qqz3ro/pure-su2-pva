module

public import KhanSL2.Factorization.OrbitStabilizerDecomposition
public import KhanSL2.SymmetricFamily.AverageBaseChange

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators TensorProduct
namespace KhanSL2.Factorization.FiberTransport

variable {R G M : Type*} [CommRing R] [Group G] [Fintype G]
  [AddCommGroup M] [Module R M]

/-- The normalized Reynolds operator for an actual linear group action. -/
def average (ρ : G →* Module.End R M) (c : R) : Module.End R M := c • ∑ g, ρ g

theorem average_mem_fixed (ρ : G →* Module.End R M) (c : R) (x : M) :
    average ρ c x ∈ fixedVectors (fun g => ρ g) := by
  intro h
  simp only [average,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum]
  congr 1
  have hm (g : G) : ρ h (ρ g x) = ρ (h*g) x := by rw [map_mul]; rfl
  simp only [hm]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun g => ρ g x)

theorem average_eq_self (ρ : G →* Module.End R M) (c : R)
    (hc : c * (Fintype.card G : R) = 1) (x : fixedVectors (fun g => ρ g)) :
    average ρ c x.val = x.val := by
  have hx : ∀ g, ρ g x.val = x.val := x.property
  simp only [average,LinearMap.smul_apply,LinearMap.sum_apply,hx,
    Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R,smul_smul,hc,one_smul]

def averageProjection (ρ : G →* Module.End R M) (c : R) :
    M →ₗ[R] fixedVectors (fun g => ρ g) :=
  (average ρ c).codRestrict _ (average_mem_fixed ρ c)

theorem averageProjection_leftInverse (ρ : G →* Module.End R M) (c : R)
    (hc : c * (Fintype.card G : R) = 1) :
    (averageProjection ρ c).comp (fixedVectors (fun g => ρ g)).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact average_eq_self ρ c hc x

/-- Normalized invariants commute with arbitrary scalar extension, for the
actual tensor maps. This includes signed permutation actions and nonreduced bases. -/
def fixedVectorsBaseChangeEquiv (S : Type*) [CommRing S] [Algebra R S]
    (ρ : G →* Module.End R M) (c : R) (hc : c * (Fintype.card G : R) = 1) :
    S ⊗[R] fixedVectors (fun g => ρ g) ≃ₗ[S]
      SymmetricFamily.fixedOperators (fun g => (ρ g).baseChange S) :=
  SymmetricFamily.splitAverageBaseChangeEquiv S
    (fixedVectors (fun g => ρ g)).subtype (averageProjection ρ c) (fun g => ρ g) c hc
    (averageProjection_leftInverse ρ c hc) (by rfl)
    (fun g => by
      ext x
      exact x.property g)

@[simp] theorem fixedVectorsBaseChangeEquiv_apply (S : Type*) [CommRing S] [Algebra R S]
    (ρ : G →* Module.End R M) (c : R) (hc : c * (Fintype.card G : R) = 1)
    (x : S ⊗[R] fixedVectors (fun g => ρ g)) :
    (fixedVectorsBaseChangeEquiv S ρ c hc x).val =
      (fixedVectors (fun g => ρ g)).subtype.baseChange S x := rfl

end KhanSL2.Factorization.FiberTransport


