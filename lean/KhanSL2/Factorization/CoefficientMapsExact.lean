module

public import KhanSL2.Factorization.CoefficientMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Relative chains preserve short exact sequences split under the constant action.
The splittings are explicit constant-equivariant linear maps; they need not
commute with positive currents. The CE differential itself remains unchanged. -/

noncomputable section
namespace KhanSL2.Factorization
open KhanSL2.BGG

variable {N M P : Type*}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]

@[simp] theorem coefficientDegreeMap_id (j : ℕ) :
    coefficientDegreeMap (LinearMap.id : N →ₗ[ℂ] N) ConstantEquivariant.id j = LinearMap.id := by
  ext z
  exact LinearMap.congr_fun (coefficientMap_id (N := N)) (z : RelativeChains N)

theorem coefficientDegreeMap_comp (f : N →ₗ[ℂ] M) (g : M →ₗ[ℂ] P)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) (j : ℕ) :
    coefficientDegreeMap (g.comp f) (hg.comp hf) j =
      (coefficientDegreeMap g hg j).comp (coefficientDegreeMap f hf j) := by
  ext z
  exact LinearMap.congr_fun (coefficientMap_comp f g hf hg) z

/-- A constant-equivariant retraction stays a retraction on every actual chain degree. -/
theorem coefficientDegreeMap_leftInverse (i : N →ₗ[ℂ] M) (r : M →ₗ[ℂ] N)
    (hi : ConstantEquivariant i) (hr : ConstantEquivariant r)
    (hri : r.comp i = LinearMap.id) (j : ℕ) :
    Function.LeftInverse (coefficientDegreeMap r hr j) (coefficientDegreeMap i hi j) := by
  have h : (coefficientMap r hr).comp (coefficientMap i hi) = LinearMap.id := by
    rw [← coefficientMap_comp]
    simp only [hri, coefficientMap_id]
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun h z

/-- A constant-equivariant section stays a section on every actual chain degree. -/
theorem coefficientDegreeMap_rightInverse (p : M →ₗ[ℂ] P) (s : P →ₗ[ℂ] M)
    (hp : ConstantEquivariant p) (hs : ConstantEquivariant s)
    (hps : p.comp s = LinearMap.id) (j : ℕ) :
    Function.RightInverse (coefficientDegreeMap s hs j) (coefficientDegreeMap p hp j) :=
  coefficientDegreeMap_leftInverse s p hs hp hps j

/-- Split coefficient sequences induce exact sequences on each relative chain group. -/
theorem coefficientDegreeMap_exact_of_split
    (i : N →ₗ[ℂ] M) (p : M →ₗ[ℂ] P) (r : M →ₗ[ℂ] N) (s : P →ₗ[ℂ] M)
    (hi : ConstantEquivariant i) (hp : ConstantEquivariant p)
    (hr : ConstantEquivariant r) (hs : ConstantEquivariant s)
    (hpi : p.comp i = 0) (hdecomp : i.comp r + s.comp p = LinearMap.id) (j : ℕ) :
    LinearMap.range (coefficientDegreeMap i hi j) =
      LinearMap.ker (coefficientDegreeMap p hp j) := by
  have hpi' : (coefficientMap p hp).comp (coefficientMap i hi) = 0 := by
    rw [← coefficientMap_comp]
    simp only [hpi, coefficientMap_zero]
  have hdecomp' : (coefficientMap i hi).comp (coefficientMap r hr) +
      (coefficientMap s hs).comp (coefficientMap p hp) = LinearMap.id := by
    rw [← coefficientMap_comp, ← coefficientMap_comp, ← coefficientMap_add]
    simp only [hdecomp, coefficientMap_id]
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    exact LinearMap.congr_fun hpi' w
  · intro z hz
    refine ⟨coefficientDegreeMap r hr j z, ?_⟩
    apply Subtype.ext
    change coefficientMap i hi (coefficientMap r hr (z : RelativeChains M)) = (z : RelativeChains M)
    have hpz : coefficientMap p hp (z : RelativeChains M) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    have h := LinearMap.congr_fun hdecomp' (z : RelativeChains M)
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, hpz, map_zero,
      add_zero, LinearMap.id_apply] using h

/-- All three short-exactness assertions follow from a specified constant splitting. -/
theorem coefficientDegreeMap_shortExact_of_split
    (i : N →ₗ[ℂ] M) (p : M →ₗ[ℂ] P) (r : M →ₗ[ℂ] N) (s : P →ₗ[ℂ] M)
    (hi : ConstantEquivariant i) (hp : ConstantEquivariant p)
    (hr : ConstantEquivariant r) (hs : ConstantEquivariant s)
    (hpi : p.comp i = 0) (hri : r.comp i = LinearMap.id)
    (hps : p.comp s = LinearMap.id) (hdecomp : i.comp r + s.comp p = LinearMap.id)
    (j : ℕ) :
    Function.Injective (coefficientDegreeMap i hi j) ∧
      LinearMap.range (coefficientDegreeMap i hi j) =
        LinearMap.ker (coefficientDegreeMap p hp j) ∧
      Function.Surjective (coefficientDegreeMap p hp j) :=
  ⟨(coefficientDegreeMap_leftInverse i r hi hr hri j).injective,
    coefficientDegreeMap_exact_of_split i p r s hi hp hr hs hpi hdecomp j,
    (coefficientDegreeMap_rightInverse p s hp hs hps j).surjective⟩

end KhanSL2.Factorization

