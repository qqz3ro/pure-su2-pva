module

public import KhanSL2.Factorization.EvenWeightBoundsTop

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped DirectSum
namespace KhanSL2.Factorization.EvenWeightBounds
open BGG

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- A split top quotient exhausts a one-dimensional top eigenspace, so its
actual invariant kernel has no top eigenvectors. -/
theorem top_quotient_kernel_eigenspace_bot (m : ℕ)
    (htop : Module.finrank ℂ ((cartan V).eigenspace (2*(m : ℂ))) = 1)
    (f : V →ₗ⁅ℂ,G⁆ Coefficient m) (j : Coefficient m →ₗ⁅ℂ,G⁆ V)
    (hfj : f.toLinearMap.comp j.toLinearMap = LinearMap.id) :
    (cartan f.ker).eigenspace (2*(m : ℂ)) = ⊥ := by
  let b : Coefficient m := TauCeti.Sl2Std.basis ℂ (2*m) 0
  have hb : b ≠ 0 := (TauCeti.Sl2Std.basis ℂ (2*m)).ne_zero 0
  have hfb : f (j b) = b := LinearMap.congr_fun hfj b
  have hjb : j b ≠ 0 := by
    intro h
    apply hb
    rw [← hfb,h,map_zero]
  have hwb : j b ∈ (cartan V).eigenspace (2*(m : ℂ)) := by
    apply Module.End.mem_eigenspace_iff.mpr
    change ⁅MatrixSL2.h,j b⁆ = _
    rw [← j.map_lie]
    have hs : ⁅MatrixSL2.h,b⁆ = (2*(m : ℂ)) • b := by
      change cartan (TauCeti.Sl2Std ℂ (2*m)) (TauCeti.Sl2Std.basis ℂ (2*m) 0) = _
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using standard_highest_eigenvector (2*m)
    rw [hs,map_smul]
  let w : (cartan V).eigenspace (2*(m : ℂ)) := ⟨j b,hwb⟩
  have hw : w ≠ 0 := fun h => hjb (congrArg Subtype.val h)
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hv' : v.val ∈ (cartan V).eigenspace (2*(m : ℂ)) := by
    apply Module.End.mem_eigenspace_iff.mpr
    exact congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hv)
  obtain ⟨c,hc⟩ := exists_smul_eq_of_finrank_eq_one htop hw
    (⟨v.val,hv'⟩ : (cartan V).eigenspace (2*(m : ℂ)))
  have he : c • j b = v.val := congrArg Subtype.val hc
  have hz : c • b = 0 := by
    calc
      c • b = c • f (j b) := by rw [hfb]
      _ = f (c • j b) := (map_smul f c (j b)).symm
      _ = f v.val := congrArg f he
      _ = 0 := v.property
  have hc0 : c = 0 := (smul_eq_zero.mp hz).resolve_right hb
  apply Subtype.ext
  change v.val = 0
  rw [← he,hc0,zero_smul]

/-- The finite sl₂ top quotient with its genuine splitting and strictly smaller
kernel constituents. This is a G-module statement; evaluation-module hypotheses
are required separately before transporting these maps to current modules. -/
theorem exists_top_split_strict_kernel (m : ℕ)
    (hp : aeval (cartan V) (evenBoundPolynomial m) = 0)
    (htop : Module.finrank ℂ ((cartan V).eigenspace (2*(m : ℂ))) = 1) :
    ∃ (f : V →ₗ⁅ℂ,G⁆ Coefficient m) (j : Coefficient m →ₗ⁅ℂ,G⁆ V),
      f.toLinearMap.comp j.toLinearMap = LinearMap.id ∧ Function.Surjective f ∧
      (cartan f.ker).eigenspace (2*(m : ℂ)) = ⊥ ∧
      ∃ (k : ℕ) (q : Fin k → ℕ), (∀ i, q i < m) ∧
        Nonempty (f.ker ≃ₗ⁅ℂ,G⁆ ⨁ i : Fin k, Coefficient (q i)) := by
  obtain ⟨j,hj⟩ := exists_top_embedding m hp htop
  obtain ⟨f,hf⟩ := BGG.exists_lie_generalizedInverse j
  have hfj : f.toLinearMap.comp j.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact hj (hf x)
  have hf_surj : Function.Surjective f := fun x => ⟨j x,LinearMap.congr_fun hfj x⟩
  have hker := top_quotient_kernel_eigenspace_bot m htop f j hfj
  refine ⟨f,j,hfj,hf_surj,hker,?_⟩
  exact exists_strict_lieModuleEquiv m
    (cartan_annihilator_submodule f.ker (evenBoundPolynomial m) hp) hker

end KhanSL2.Factorization.EvenWeightBounds


