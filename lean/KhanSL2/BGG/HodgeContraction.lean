module

public import TauCeti.Algebra.Homology.Contraction.Linear

@[expose] public section

/-! Algebraic Hodge contraction from a proved Green-operator identity.
This is a general linear-algebra construction. It does not assert the
current-algebra Laplace formula or assume any BGG exactness. -/

noncomputable section
namespace KhanSL2.BGG

variable {R M N : Type*} [Semiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A generalized inverse of the Laplacian produces a special contraction.
The concrete Laplacian identity and harmonic projection must be supplied as
proved hypotheses when applying this construction. -/
def contractionOfLaplacian
    (d δ green : Module.End R M) (incl : N →ₗ[R] M) (proj : M →ₗ[R] N)
    (hpi : proj.comp incl = LinearMap.id)
    (hdi : d.comp incl = 0) (hpd : proj.comp d = 0)
    (hδδ : δ * δ = 0)
    (hgd : Commute green d) (hgδ : Commute green δ)
    (hgi : green.comp incl = 0) (hpδ : proj.comp δ = 0)
    (hlap : (d * δ + δ * d) * green = 1 - incl.comp proj) :
    TauCeti.LinearSpecialContraction d (0 : Module.End R N) where
  incl := incl
  proj := proj
  homotopy := δ * green
  dM_comp_incl := by simpa using hdi
  proj_comp_dM := by simpa using hpd
  proj_comp_incl := hpi
  dM_comp_homotopy_add_homotopy_comp_dM := by
    change d * (δ * green) + (δ * green) * d = 1 - incl.comp proj
    calc
      d * (δ * green) + (δ * green) * d = (d * δ + δ * d) * green := by
        simp only [add_mul, mul_assoc]
        rw [hgd.eq]
      _ = _ := hlap
  homotopy_comp_incl := by
    ext x
    change δ (green (incl x)) = 0
    have h := LinearMap.congr_fun hgi x
    change green (incl x) = 0 at h
    rw [h, map_zero]
  proj_comp_homotopy := by
    ext x
    exact LinearMap.congr_fun hpδ (green x)
  homotopy_comp_homotopy := by
    ext x
    change δ (green (δ (green x))) = 0
    have h := LinearMap.congr_fun hgδ.eq (green x)
    change green (δ (green x)) = δ (green (green x)) at h
    rw [h]
    exact LinearMap.congr_fun hδδ (green (green x))

end KhanSL2.BGG