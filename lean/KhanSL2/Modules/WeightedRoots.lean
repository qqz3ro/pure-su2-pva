module

public import KhanSL2.Modules.PolynomialModels
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# The weighted-root substitution

The map from symmetric polynomials on `r + 3*s` roots sends `r` roots to the
first alphabet and three labelled copies of each of the `s` remaining roots
to the second alphabet. Block symmetry is proved by lifting each block
permutation to a permutation of the labelled roots.
-/

noncomputable section

namespace KhanSL2.Modules

open MvPolynomial

/-- Labelled root positions: one copy of each `z`, three copies of each `w`. -/
abbrev RootSlots (r s : ℕ) := Fin r ⊕ (Fin 3 × Fin s)

/-- The explicit enumeration of the weighted root positions. -/
def rootIndexEquiv (r s : ℕ) : RootSlots r s ≃ Fin (r + 3 * s) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) finProdFinEquiv).trans finSumFinEquiv

/-- Forget the copy label on a root of multiplicity three. -/
def rootProjection (r s : ℕ) : RootSlots r s → Fin r ⊕ Fin s
  | Sum.inl i => Sum.inl i
  | Sum.inr (_, j) => Sum.inr j

/-- Which polynomial variable is substituted for a labelled root. -/
def weightedRootIndex (r s : ℕ) : Fin (r + 3 * s) → Fin r ⊕ Fin s :=
  rootProjection r s ∘ (rootIndexEquiv r s).symm

@[simp] theorem weightedRootIndex_rootIndexEquiv (r s : ℕ) (a : RootSlots r s) :
    weightedRootIndex r s (rootIndexEquiv r s a) = rootProjection r s a := by
  simp [weightedRootIndex]

/-- A block permutation lifted to all the labelled roots. -/
def rootPermutation {r s : ℕ} (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    Equiv.Perm (Fin (r + 3 * s)) :=
  (rootIndexEquiv r s).symm.trans
    ((Equiv.sumCongr e (Equiv.prodCongr (Equiv.refl (Fin 3)) f)).trans (rootIndexEquiv r s))

theorem weightedRootIndex_permutation {r s : ℕ}
    (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) (i : Fin (r + 3 * s)) :
    weightedRootIndex r s (rootPermutation e f i) =
      Equiv.sumCongr e f (weightedRootIndex r s i) := by
  obtain ⟨a, rfl⟩ := (rootIndexEquiv r s).surjective i
  cases a with
  | inl a => simp [rootPermutation, weightedRootIndex, rootProjection]
  | inr a => simp [rootPermutation, weightedRootIndex, rootProjection]

theorem weightedRootSubstitution_symmetric (r s : ℕ) (q : R (r + 3 * s)) :
    IsBlockSymmetric (rename (weightedRootIndex r s) (q : MvPolynomial (Fin (r + 3 * s)) ℂ)) := by
  intro e f
  rw [rename_rename]
  have h : (Equiv.sumCongr e f : Fin r ⊕ Fin s → Fin r ⊕ Fin s) ∘ weightedRootIndex r s =
      weightedRootIndex r s ∘ (rootPermutation e f : Fin (r + 3 * s) → Fin (r + 3 * s)) := by
    funext i
    exact (weightedRootIndex_permutation e f i).symm
  rw [h, ← rename_rename, q.property (rootPermutation e f)]

/-- The weighted-root map `ν* : R_(r+3s) → S_(r,s)`. -/
def nu (r s : ℕ) : R (r + 3 * s) →ₐ[ℂ] S r s :=
  ((rename (weightedRootIndex r s)).comp
    (MvPolynomial.symmetricSubalgebra (Fin (r + 3 * s)) ℂ).val).codRestrict
      (blockSymmetric r s) (weightedRootSubstitution_symmetric r s)

@[simp] theorem nu_coe (r s : ℕ) (q : R (r + 3 * s)) :
    (nu r s q : Polynomial r s) =
      rename (weightedRootIndex r s) (q : MvPolynomial (Fin (r + 3 * s)) ℂ) := rfl

/-- Power sums, bundled as elements of the coefficient ring. -/
def powerSum (B m : ℕ) : R B :=
  ⟨MvPolynomial.psum (Fin B) ℂ m, MvPolynomial.psum_isSymmetric (Fin B) ℂ m⟩

/-- The map has multiplicities one and three, including in degree zero. -/
theorem nu_powerSum (r s m : ℕ) :
    (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) =
      rename Sum.inl (MvPolynomial.psum (Fin r) ℂ m) +
        (3 : Polynomial r s) * rename Sum.inr (MvPolynomial.psum (Fin s) ℂ m) := by
  change rename (weightedRootIndex r s) (MvPolynomial.psum (Fin (r + 3 * s)) ℂ m) = _
  simp only [MvPolynomial.psum, map_sum, map_pow, rename_X]
  rw [← (rootIndexEquiv r s).sum_comp
    (fun i => (X (weightedRootIndex r s i) : Polynomial r s) ^ m)]
  simp only [weightedRootIndex_rootIndexEquiv, Fintype.sum_sum_type,
    Fintype.sum_prod_type, rootProjection, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

/-- The explicit scalar action avoids ambiguity with the ambient polynomial scalar action. -/
instance (priority := 2000) jSMul (r s : ℕ) : SMul (R (r + 3 * s)) (J r s) :=
  ⟨fun a q => (nu r s a : S r s) • q⟩

/-- The coefficient-ring action on the actual polynomial module. -/
instance jModule (r s : ℕ) : Module (R (r + 3 * s)) (J r s) :=
  Module.compHom (J r s) (nu r s).toRingHom

@[simp] theorem j_smul_coe (r s : ℕ) (a : R (r + 3 * s)) (q : J r s) :
    (a • q : J r s).val = (nu r s a : Polynomial r s) * q.val := rfl

instance jScalarTower (r s : ℕ) : IsScalarTower ℂ (R (r + 3 * s)) (J r s) where
  smul_assoc c a q := by
    change nu r s (c • a) • q = c • (nu r s a • q)
    rw [map_smul, smul_assoc]

end KhanSL2.Modules


