module

public import KhanSL2.Macdonald.FinitePieces
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The complex-bilinear restricted-dual pairing. Polynomial monomials have
factorial norms. This is the symmetric tensor pairing, not the Hermitian
Hodge pairing. Perfectness is asserted only on the proved finite pieces. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- Multiplicity factorial for the symmetric tensor monomial. -/
def exponentFactorial (d : Exponent) : ℕ := d.prod (fun _ n => n.factorial)

@[simp] theorem exponentFactorial_zero : exponentFactorial 0 = 1 := by
  simp [exponentFactorial]

theorem exponentFactorial_ne_zero (d : Exponent) : exponentFactorial d ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => Nat.factorial_ne_zero _)

/-- Bilinear evaluation of a restricted cochain on a symmetric/exterior chain. -/
def pairing : W →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  basis.constr ℂ (fun b => (exponentFactorial b.1 : ℂ) • basis.coord b)

@[simp] theorem pairing_basis_left (b : BasisIndex) (u : W) :
    pairing (basis b) u = (exponentFactorial b.1 : ℂ) * basis.repr u b := by
  simp [pairing, Module.Basis.coord_apply]

@[simp] theorem pairing_basis (b c : BasisIndex) :
    pairing (basis b) (basis c) = if b = c then (exponentFactorial b.1 : ℂ) else 0 := by
  classical
  simp only [pairing_basis_left, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : b = c
  · subst c; simp
  · simp [h, Ne.symm h]

theorem pairing_symm (u v : W) : pairing u v = pairing v u := by
  have h : pairing = pairing.flip := by
    apply basis.ext
    intro b
    apply basis.ext
    intro c
    change pairing (basis b) (basis c) = pairing (basis c) (basis b)
    by_cases hbc : b = c
    · subst c; rfl
    · simp [hbc, Ne.symm hbc]
  exact LinearMap.congr_fun (LinearMap.congr_fun h u) v

@[simp] theorem pairing_basis_right (u : W) (b : BasisIndex) :
    pairing u (basis b) = (exponentFactorial b.1 : ℂ) * basis.repr u b := by
  rw [pairing_symm, pairing_basis_left]

theorem pairing_nondegenerate {u : W} (h : ∀ v, pairing u v = 0) : u = 0 := by
  apply basis.repr.injective
  ext b
  have hb := h (basis b)
  rw [pairing_basis_right] at hb
  have hn : (exponentFactorial b.1 : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero b.1)
  simpa only [map_zero, Finsupp.zero_apply] using (mul_eq_zero.mp hb).resolve_left hn

/-- Restrict both arguments to one homogeneous finite-dimensional piece. -/
def piecePairing (w s k : ℕ) : piece w s k →ₗ[ℂ] Module.Dual ℂ (piece w s k) :=
  { toFun := fun u => (pairing u.val).comp (piece w s k).subtype
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

@[simp] theorem piecePairing_apply (w s k : ℕ) (u v : piece w s k) :
    piecePairing w s k u v = pairing u.val v.val := rfl

theorem piecePairing_injective (w s k : ℕ) :
    Function.Injective (piecePairing w s k) := by
  classical
  apply (LinearMap.ker_eq_bot (R := ℂ) (R₂ := ℂ) (M := piece w s k)
    (M₂ := Module.Dual ℂ (piece w s k)) (f := piecePairing w s k)).mp
  apply eq_bot_iff.mpr
  intro u hu
  have hz : piecePairing w s k u = 0 := hu
  apply Subtype.ext
  apply basis.repr.injective
  ext b
  by_cases hb : b ∈ (basis.repr u.val).support
  · obtain ⟨hw, hs, hk⟩ := (mem_piece_iff u.val w s k).mp u.property b hb
    have hm : basis b ∈ piece w s k := by
      simpa only [hw, hs, hk] using basis_mem_piece b
    have hv := LinearMap.congr_fun hz ⟨basis b, hm⟩
    change pairing u.val (basis b) = 0 at hv
    rw [pairing_basis_right] at hv
    have hn : (exponentFactorial b.1 : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero b.1)
    simpa using (mul_eq_zero.mp hv).resolve_left hn
  · simp [Finsupp.notMem_support_iff.mp hb]

/-- Actual perfect duality, independently of any FGT assumption. -/
def pieceDualEquiv (w s k : ℕ) :
    piece w s k ≃ₗ[ℂ] Module.Dual ℂ (piece w s k) := by
  letI : FiniteDimensional ℂ (Module.Dual ℂ (piece w s k)) :=
    Subspace.instModuleDualFiniteDimensional (K := ℂ) (V := piece w s k)
  exact LinearEquiv.ofInjectiveOfFinrankEq (K := ℂ) (V := piece w s k)
    (V' := Module.Dual ℂ (piece w s k)) (piecePairing w s k)
    (piecePairing_injective w s k) (Subspace.dual_finrank_eq (K := ℂ) (V := piece w s k)).symm

@[simp] theorem pieceDualEquiv_apply (w s k : ℕ) (u v : piece w s k) :
    pieceDualEquiv w s k u v = pairing u.val v.val := rfl

end KhanSL2.Macdonald
