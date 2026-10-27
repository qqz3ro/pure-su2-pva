module

public import KhanSL2.Modules.WeightedRoots

@[expose] public section

/-!
# The polynomial modules indexed by coefficient and form degree

For an admissible pair `(B,p)`, put `s=(B-p)/3` and use the actual polynomial
module `J p s`. For the other pairs use the zero polynomial submodule. The
coefficient ring acts through weighted-root substitution in admissible sectors.
-/

noncomputable section

namespace KhanSL2.Modules

/-- Number of odd source factors in the sector, when it exists. -/
def sectorS (B p : ℕ) : ℕ := (B - p) / 3

/-- The coefficient/form degrees occur in the source. -/
def ValidSector (B p : ℕ) : Prop := B = p + 3 * sectorS B p

theorem sectorS_of_eq {B p s : ℕ} (h : B = p + 3 * s) : sectorS B p = s := by
  subst B
  simp [sectorS]

theorem validSector_iff (B p : ℕ) : ValidSector B p ↔ ∃ s : ℕ, B = p + 3 * s := by
  constructor
  · intro h
    exact ⟨sectorS B p, h⟩
  · rintro ⟨s, hs⟩
    change B = p + 3 * sectorS B p
    rw [sectorS_of_eq hs]
    exact hs

/-- Relabelling a coefficient ring along equality of its number of roots. -/
def ringCast {B C : ℕ} (h : B = C) : R B ≃ₐ[ℂ] R C := by
  subst C
  exact AlgEquiv.refl

/-- Weighted-root substitution in a valid sector; the zero-root evaluation outside it. -/
def nuB (B p : ℕ) : R B →ₐ[ℂ] S p (sectorS B p) := by
  classical
  exact if h : ValidSector B p then
    (nu p (sectorS B p)).comp (ringCast h).toAlgHom
  else
    (Algebra.ofId ℂ (S p (sectorS B p))).comp
      ((MvPolynomial.aeval fun _ : Fin B => (0 : ℂ)).comp
        (MvPolynomial.symmetricSubalgebra (Fin B) ℂ).val)

/-- The actual polynomial submodule for `(B,p)`, zero in nonexistent sectors. -/
def JBSubmodule (B p : ℕ) : Submodule (S p (sectorS B p)) (Polynomial p (sectorS B p)) := by
  classical
  exact if ValidSector B p then JSubmodule p (sectorS B p) else ⊥

/-- `J_{B,p}` with its concrete polynomial carrier. -/
abbrev JB (B p : ℕ) := ↥(JBSubmodule B p)

theorem JBSubmodule_of_valid {B p : ℕ} (h : ValidSector B p) :
    JBSubmodule B p = JSubmodule p (sectorS B p) := by
  simp [JBSubmodule, h]

theorem JBSubmodule_of_invalid {B p : ℕ} (h : ¬ValidSector B p) :
    JBSubmodule B p = ⊥ := by
  simp [JBSubmodule, h]

theorem mem_JBSubmodule_of_valid {B p : ℕ} (h : ValidSector B p)
    (q : Polynomial p (sectorS B p)) :
    q ∈ JBSubmodule B p ↔ q ∈ JSubmodule p (sectorS B p) := by
  rw [JBSubmodule_of_valid h]

theorem jb_eq_zero_of_invalid {B p : ℕ} (h : ¬ValidSector B p) (q : JB B p) : q = 0 := by
  apply Subtype.ext
  exact (show JBSubmodule B p ≤ ⊥ from (JBSubmodule_of_invalid h).le) q.property

instance (priority := 2000) jbSMul (B p : ℕ) : SMul (R B) (JB B p) :=
  ⟨fun a q => (nuB B p a : S p (sectorS B p)) • q⟩

/-- The `R_B` action is the actual multiplication by the weighted-root image. -/
instance jbModule (B p : ℕ) : Module (R B) (JB B p) :=
  Module.compHom (JB B p) (nuB B p).toRingHom

@[simp] theorem jb_smul_coe (B p : ℕ) (a : R B) (q : JB B p) :
    (a • q : JB B p).val = (nuB B p a : Polynomial p (sectorS B p)) * q.val := rfl

instance jbScalarTower (B p : ℕ) : IsScalarTower ℂ (R B) (JB B p) where
  smul_assoc c a q := by
    change nuB B p (c • a) • q = c • (nuB B p a • q)
    rw [map_smul, smul_assoc]

/-- In an admissible sector, the polynomial carrier is exactly the previously defined `J`. -/
def jToJB (B p : ℕ) (h : ValidSector B p) : J p (sectorS B p) ≃ₗ[ℂ] JB B p where
  toFun q := ⟨q.val, (mem_JBSubmodule_of_valid h q.val).mpr q.property⟩
  invFun q := ⟨q.val, (mem_JBSubmodule_of_valid h q.val).mp q.property⟩
  left_inv _q := rfl
  right_inv _q := rfl
  map_add' _q _t := rfl
  map_smul' _c _q := rfl

@[simp] theorem jToJB_coe (B p : ℕ) (h : ValidSector B p) (q : J p (sectorS B p)) :
    (jToJB B p h q).val = q.val := rfl

/-- The valid-sector equivalence with the odd-factor count supplied explicitly. -/
def jToJB_of_eq {B p s : ℕ} (h : B = p + 3 * s) : J p s ≃ₗ[ℂ] JB B p := by
  have hs := sectorS_of_eq h
  subst s
  exact jToJB B p h

end KhanSL2.Modules


