module

public import KhanSL2.Modules.DepthPolynomialComparison

@[expose] public section

/-! # The depth presentation of the indexed polynomial modules `JB` -/

noncomputable section

namespace KhanSL2.Modules

/-- The two admissibility tests have exactly the same arithmetic content. -/
theorem validSector_iff_depth (B p : ℕ) :
    ValidSector B p ↔ p ≤ B ∧ 3 ∣ B - p := by
  rw [validSector_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨by omega, s, ?_⟩
    omega
  · rintro ⟨hp, s, hs⟩
    exact ⟨s, by omega⟩

/-- The indexed polynomial carriers agree, including the zero sectors. -/
theorem mem_depthJB_iff (B p : ℕ) (q : Polynomial p (sectorS B p)) :
    (show Depth.RootsMod B p ((B - p) / 3) from q) ∈ Depth.JB B p ↔
      q ∈ JBSubmodule B p := by
  classical
  by_cases h : ValidSector B p
  · rw [Depth.JB, if_pos ((validSector_iff_depth B p).mp h), JBSubmodule_of_valid h]
    exact mem_depthJ_iff B p (sectorS B p) q
  · rw [Depth.JB, if_neg (fun hd => h ((validSector_iff_depth B p).mpr hd)),
      JBSubmodule_of_invalid h]
    rfl

/-- Elementary coordinates intertwine the indexed scalar maps in every valid sector. -/
theorem nuB_depthCoefficientEquiv (B p : ℕ) (h : ValidSector B p) (q : Depth.RB B) :
    (nuB B p (elementaryAlgEquiv B q) : Polynomial p (sectorS B p)) =
      Depth.nuStar B p (sectorS B p) q := by
  unfold nuB
  rw [dif_pos h]
  exact nu_depthCoefficientEquiv_of_eq h q

/-- Identity on actual polynomials, with the coefficient-ring coordinates changed explicitly. -/
def depthJBEquiv (B p : ℕ) :
    ↥(Depth.JB B p) ≃ₛₗ[(elementaryAlgEquiv B).toRingHom] JB B p where
  toFun q := ⟨q.val, (mem_depthJB_iff B p q.val).mp q.property⟩
  invFun q := ⟨q.val, (mem_depthJB_iff B p q.val).mpr q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a q := by
    apply Subtype.ext
    change Depth.nuStar B p (sectorS B p) a * (show Polynomial p (sectorS B p) from q.val) =
      (nuB B p (elementaryAlgEquiv B a) : Polynomial p (sectorS B p)) * (show Polynomial p (sectorS B p) from q.val)
    by_cases h : ValidSector B p
    · rw [nuB_depthCoefficientEquiv B p h]
    · have hq : (show Polynomial p (sectorS B p) from q.val) = 0 :=
        (show JBSubmodule B p ≤ ⊥ from (JBSubmodule_of_invalid h).le)
          ((mem_depthJB_iff B p q.val).mp q.property)
      rw [hq, mul_zero, mul_zero]

@[simp] theorem depthJBEquiv_coe (B p : ℕ) (q : ↥(Depth.JB B p)) :
    (depthJBEquiv B p q).val = (show Polynomial p (sectorS B p) from q.val) := rfl

end KhanSL2.Modules

