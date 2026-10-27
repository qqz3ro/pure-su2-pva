module

public import KhanSL2.Macdonald.Pairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Transposition in the restricted dual, using the actual finite weight and
symmetric-degree blocks. No duality assertion for an infinite tensor product
is used. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

theorem mem_weightDegreePiece_iff (u : W) (w s : ℕ) :
    u ∈ weightDegreePiece w s ↔ ∀ b ∈ (basis.repr u).support,
      weight b = w ∧ symmetricDegree b = s := Iff.rfl

theorem basis_mem_weightDegreePiece (b : BasisIndex) :
    basis b ∈ weightDegreePiece (weight b) (symmetricDegree b) := by
  change basis.repr (basis b) ∈ Finsupp.supported ℂ ℂ _
  rw [Module.Basis.repr_self]
  exact Finsupp.single_mem_supported ℂ 1 ⟨rfl, rfl⟩

/-- Restricted evaluation on a whole finite weight/symmetric-degree block. -/
def weightPairing (w s : ℕ) :
    weightDegreePiece w s →ₗ[ℂ] Module.Dual ℂ (weightDegreePiece w s) :=
  { toFun := fun u => (pairing u.val).comp (weightDegreePiece w s).subtype
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

@[simp] theorem weightPairing_apply (w s : ℕ) (u v : weightDegreePiece w s) :
    weightPairing w s u v = pairing u.val v.val := rfl

theorem weightPairing_injective (w s : ℕ) : Function.Injective (weightPairing w s) := by
  classical
  apply (LinearMap.ker_eq_bot (R := ℂ) (R₂ := ℂ) (M := weightDegreePiece w s)
    (M₂ := Module.Dual ℂ (weightDegreePiece w s)) (f := weightPairing w s)).mp
  apply eq_bot_iff.mpr
  intro u hu
  have hz : weightPairing w s u = 0 := hu
  apply Subtype.ext
  apply basis.repr.injective
  ext b
  by_cases hb : b ∈ (basis.repr u.val).support
  · obtain ⟨hw, hs⟩ := (mem_weightDegreePiece_iff u.val w s).mp u.property b hb
    have hm : basis b ∈ weightDegreePiece w s := by
      simpa only [hw, hs] using basis_mem_weightDegreePiece b
    have hv := LinearMap.congr_fun hz ⟨basis b, hm⟩
    change pairing u.val (basis b) = 0 at hv
    rw [pairing_basis_right] at hv
    have hn : (exponentFactorial b.1 : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero b.1)
    simpa using (mul_eq_zero.mp hv).resolve_left hn
  · simp [Finsupp.notMem_support_iff.mp hb]

/-- Perfect duality on the finite block, prior to taking invariants or homology. -/
def weightDualEquiv (w s : ℕ) :
    weightDegreePiece w s ≃ₗ[ℂ] Module.Dual ℂ (weightDegreePiece w s) := by
  letI : FiniteDimensional ℂ (Module.Dual ℂ (weightDegreePiece w s)) :=
    Subspace.instModuleDualFiniteDimensional (K := ℂ) (V := weightDegreePiece w s)
  exact LinearEquiv.ofInjectiveOfFinrankEq (K := ℂ) (V := weightDegreePiece w s)
    (V' := Module.Dual ℂ (weightDegreePiece w s)) (weightPairing w s)
    (weightPairing_injective w s) (Subspace.dual_finrank_eq (K := ℂ) (V := weightDegreePiece w s)).symm

@[simp] theorem weightDualEquiv_apply (w s : ℕ) (u v : weightDegreePiece w s) :
    weightDualEquiv w s u v = pairing u.val v.val := rfl

theorem pairing_blocks_eq_zero {w s w' s' : ℕ} {u v : W}
    (hu : u ∈ weightDegreePiece w s) (hv : v ∈ weightDegreePiece w' s')
    (hne : (w,s) ≠ (w',s')) : pairing u v = 0 := by
  classical
  rw [eq_sum_basis u, map_sum]
  simp only [LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro b hb
  rw [pairing_basis_left]
  have hcoeff : basis.repr v b = 0 := by
    by_contra hn
    obtain ⟨hw,hs⟩ := (mem_weightDegreePiece_iff u w s).mp hu b hb
    obtain ⟨hw',hs'⟩ := (mem_weightDegreePiece_iff v w' s').mp hv b
      (Finsupp.mem_support_iff.mpr hn)
    exact hne (Prod.ext (hw.symm.trans hw') (hs.symm.trans hs'))
  simp [hcoeff]

/-- Preserve the two degrees which make each whole CE block finite. -/
def PreservesWeightDegree (D : Module.End ℂ W) : Prop :=
  ∀ w s, ∀ u ∈ weightDegreePiece w s, D u ∈ weightDegreePiece w s

/-- The transpose of one row, represented in its actual finite block. -/
def transposeBasis (D : Module.End ℂ W) (b : BasisIndex) : W :=
  ((weightDualEquiv (weight b) (symmetricDegree b)).symm
    ((pairing (basis b)).comp (D.comp
      (weightDegreePiece (weight b) (symmetricDegree b)).subtype))).val

theorem transposeBasis_mem (D : Module.End ℂ W) (b : BasisIndex) :
    transposeBasis D b ∈ weightDegreePiece (weight b) (symmetricDegree b) :=
  Subtype.property _

theorem pairing_transposeBasis_same (D : Module.End ℂ W) (b : BasisIndex)
    (v : weightDegreePiece (weight b) (symmetricDegree b)) :
    pairing (transposeBasis D b) v.val = pairing (basis b) (D v.val) := by
  have h := LinearMap.congr_fun
    ((weightDualEquiv (weight b) (symmetricDegree b)).apply_symm_apply
      ((pairing (basis b)).comp (D.comp
        (weightDegreePiece (weight b) (symmetricDegree b)).subtype))) v
  exact h

/-- The restricted transpose of a block-preserving operator; the degree
preservation is required by its transpose theorem, not assumed by its definition. -/
def restrictedTranspose (D : Module.End ℂ W) : Module.End ℂ W :=
  basis.constr ℂ (transposeBasis D)

@[simp] theorem restrictedTranspose_basis (D : Module.End ℂ W) (b : BasisIndex) :
    restrictedTranspose D (basis b) = transposeBasis D b :=
  basis.constr_basis ℂ _ b

theorem pairing_restrictedTranspose (D : Module.End ℂ W) (hD : PreservesWeightDegree D)
    (u v : W) : pairing (restrictedTranspose D u) v = pairing u (D v) := by
  have h : pairing.comp (restrictedTranspose D) =
      pairing.compl₂ D := by
    apply basis.ext
    intro b
    apply basis.ext
    intro c
    change pairing (restrictedTranspose D (basis b)) (basis c) =
      pairing (basis b) (D (basis c))
    rw [restrictedTranspose_basis]
    by_cases he : (weight b, symmetricDegree b) = (weight c, symmetricDegree c)
    · have hc : basis c ∈ weightDegreePiece (weight b) (symmetricDegree b) := by
        have hw : weight b = weight c := congrArg Prod.fst he
        have hs : symmetricDegree b = symmetricDegree c := congrArg Prod.snd he
        simpa only [hw,hs] using basis_mem_weightDegreePiece c
      exact pairing_transposeBasis_same D b ⟨basis c,hc⟩
    · rw [pairing_blocks_eq_zero (transposeBasis_mem D b)
        (basis_mem_weightDegreePiece c) he,
        pairing_blocks_eq_zero (basis_mem_weightDegreePiece b)
          (hD _ _ _ (basis_mem_weightDegreePiece c)) he]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

/-- The constructed transpose remains inside each finite block. -/
theorem restrictedTranspose_mem_weightDegree (D : Module.End ℂ W)
    {w s : ℕ} {u : W} (hu : u ∈ weightDegreePiece w s) :
    restrictedTranspose D u ∈ weightDegreePiece w s := by
  rw [eq_sum_basis u, map_sum]
  apply Submodule.sum_mem
  intro b hb
  rw [map_smul, restrictedTranspose_basis]
  apply Submodule.smul_mem
  obtain ⟨hw,hs⟩ := (mem_weightDegreePiece_iff u w s).mp hu b hb
  simpa only [hw,hs] using transposeBasis_mem D b

/-- Square-zero transfers to the restricted dual without any FGT assumption. -/
theorem restrictedTranspose_square_zero (D : Module.End ℂ W)
    (hD : PreservesWeightDegree D) (hd : D.comp D = 0) (u : W) :
    restrictedTranspose D (restrictedTranspose D u) = 0 := by
  apply pairing_nondegenerate
  intro v
  rw [pairing_restrictedTranspose D hD, pairing_restrictedTranspose D hD]
  have h := LinearMap.congr_fun hd v
  change D (D v) = 0 at h
  rw [h, map_zero]

end KhanSL2.Macdonald
