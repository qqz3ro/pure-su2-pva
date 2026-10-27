module

public import KhanSL2.Factorization.FiniteDegreeTensor
public import KhanSL2.Factorization.TensorHomogeneousScalars

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module ℂ N]
  [LieRingModule Current M] [LieModule ℂ Current M]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- The finite diagonal family uses the actual homogeneous cycle quotients. -/
abbrev HomologyDegreeSum (p : ℕ) :=
  ⨁ q : Fin (p+1), Homology M q.val ⊗[ℂ] Homology N (p-q.val)

/-- Field Künneth in one degree, with its canonical cross-product map. -/
def homogeneousKunnethEquiv (p : ℕ) : HomologyDegreeSum M N p ≃ₗ[ℂ] TensorHomology M N p :=
  (DFinsupp.mapRange.linearEquiv (fun q : Fin (p+1) =>
    TensorProduct.congr (complexHomologyEquiv M q.val).symm
      (complexHomologyEquiv N (p-q.val)).symm)).trans
    ((GradedTensorTotal.finiteTermEquiv (fun q => (complex M).homology q)
      (fun q => (complex N).homology q) p).trans
      (((asIso (HomologicalComplex.homologyKunneth (complex M) (complex N) p)).toLinearEquiv).trans
        (tensorComplexHomologyEquiv M N p)))

/-- The canonical finite degree sum includes into the tensor of total homologies. -/
def homologyDegreeSumInclusion (p : ℕ) :
    HomologyDegreeSum M N p →ₗ[ℂ] TotalHomology M ⊗[ℂ] TotalHomology N :=
  DirectSum.toModule ℂ (Fin (p+1)) _ (fun q =>
    TensorProduct.map (homogeneousHomologyInclusion M q.val)
      (homogeneousHomologyInclusion N (p-q.val)))

private theorem mapRangeEquiv_single {ι : Type*} [DecidableEq ι] {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
    (e : ∀ i, A i ≃ₗ[ℂ] B i) (i : ι) (z : A i) :
    DFinsupp.mapRange.linearEquiv e (DirectSum.of A i z) = DirectSum.of B i (e i z) := by
  change DFinsupp.mapRange (fun i x => e i x) (fun i => (e i).map_zero)
    (DFinsupp.single i z) = DFinsupp.single i (e i z)
  rw [DFinsupp.mapRange_single]

theorem homogeneousKunnethEquiv_of_tmul (p : ℕ) (q : Fin (p+1))
    (u : Homology M q.val) (v : Homology N (p-q.val)) :
    homogeneousKunnethEquiv M N p (DirectSum.of
      (fun q : Fin (p+1) => Homology M q.val ⊗[ℂ] Homology N (p-q.val)) q (u ⊗ₜ[ℂ] v)) =
      tensorComplexHomologyEquiv M N p
        ((HomologicalComplex.homologyCross (complex M) (complex N) q.val (p-q.val) p
          (by have h:=q.isLt; omega)).hom
          ((complexHomologyEquiv M q.val).symm u ⊗ₜ[ℂ]
            (complexHomologyEquiv N (p-q.val)).symm v)) := by
  let A : ℕ → ModuleCat ℂ := fun q => (complex M).homology q
  let B : ℕ → ModuleCat ℂ := fun q => (complex N).homology q
  let e := fun i : Fin (p+1) => TensorProduct.congr (complexHomologyEquiv M i.val).symm
    (complexHomologyEquiv N (p-i.val)).symm
  let w := (complexHomologyEquiv M q.val).symm u ⊗ₜ[ℂ]
    (complexHomologyEquiv N (p-q.val)).symm v
  have hm := mapRangeEquiv_single
    (A:=fun i : Fin (p+1) => Homology M i.val ⊗[ℂ] Homology N (p-i.val))
    (B:=fun i : Fin (p+1) => A i.val ⊗[ℂ] B (p-i.val)) e q (u ⊗ₜ[ℂ] v)
  have h₁ := congrArg (fun z => tensorComplexHomologyEquiv M N p
    ((asIso (HomologicalComplex.homologyKunneth (complex M) (complex N) p)).toLinearEquiv
      (GradedTensorTotal.finiteTermEquiv A B p z))) hm
  have h₂ := congrArg (fun z => tensorComplexHomologyEquiv M N p
    ((HomologicalComplex.homologyKunneth (complex M) (complex N) p).hom z))
      (GradedTensorTotal.finiteToTerm_of A B p q w)
  have h₃ := congrArg (fun f => tensorComplexHomologyEquiv M N p (f.hom w))
    (HomologicalComplex.ι_homologyKunneth (complex M) (complex N) p q.val (p-q.val)
      (by have h:=q.isLt; omega))
  exact h₁.trans (h₂.trans h₃)

private theorem totalKunnethEquiv_homogeneous_add (a b p : ℕ) (h:a+b=p)
    (u : (complex M).homology a) (v : (complex N).homology b) :
    totalKunnethEquiv M N
      (homogeneousHomologyInclusion M a (complexHomologyEquiv M a u) ⊗ₜ[ℂ]
        homogeneousHomologyInclusion N b (complexHomologyEquiv N b v)) =
      (tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N)
        (tensorComplexHomologyEquiv M N p
          ((HomologicalComplex.homologyCross (complex M) (complex N) a b p h).hom (u ⊗ₜ[ℂ] v))) := by
  subst p
  exact totalKunnethEquiv_homogeneous M N a b u v

/-- The degreewise map is literally the restriction of the original total Künneth cross product. -/
theorem homogeneousKunnethEquiv_inclusion (p : ℕ) (z : HomologyDegreeSum M N p) :
    (tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N)
      (homogeneousKunnethEquiv M N p z) =
      totalKunnethEquiv M N (homologyDegreeSumInclusion M N p z) := by
  induction z using DirectSum.induction_on with
  | zero =>
    rw [(homogeneousKunnethEquiv M N p).map_zero,
      ((tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N)).map_zero,
      (homologyDegreeSumInclusion M N p).map_zero,(totalKunnethEquiv M N).map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | of q z =>
    induction z using TensorProduct.induction_on with
    | zero =>
      rw [(DirectSum.of _ q).map_zero,(homogeneousKunnethEquiv M N p).map_zero,
        ((tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N)).map_zero,
        (homologyDegreeSumInclusion M N p).map_zero,(totalKunnethEquiv M N).map_zero]
    | add x y hx hy => simp only [map_add,hx,hy]
    | tmul u v =>
      rw [homogeneousKunnethEquiv_of_tmul]
      change _ = totalKunnethEquiv M N ((DirectSum.toModule ℂ (Fin (p+1)) _ _) _)
      rw [← DirectSum.lof_eq_of ℂ,DirectSum.toModule_lof,TensorProduct.map_tmul]
      have he := totalKunnethEquiv_homogeneous_add M N q.val (p-q.val) p
        (by have h:=q.isLt; omega) ((complexHomologyEquiv M q.val).symm u)
        ((complexHomologyEquiv N (p-q.val)).symm v)
      simpa only [LinearEquiv.apply_symm_apply] using he.symm

end KhanSL2.Factorization
