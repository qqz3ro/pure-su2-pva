module

public import KhanSL2.SymmetricFamily.RootPermutation
public import KhanSL2.SymmetricFamily.RootFactorAlgebra

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The distinguished root-assignment component has precisely the two prescribed
ordered root systems, with their original factor equations. -/

noncomputable section
open Polynomial
open scoped BigOperators TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization.WeightedRoots

/-- The complement of the first block is exactly the second labelled block. -/
theorem firstBlock_compl (r s : ℕ) :
    (firstBlock r s).valᶜ = Finset.univ.map (Fin.natAddEmb r) := by
  ext i
  simp only [Finset.mem_compl, firstBlock, Finset.mem_map, Finset.mem_univ, true_and,
    Fin.castAddEmb_apply, Fin.natAddEmb_apply]
  constructor
  · intro hi
    have hir : r ≤ i.val := by
      by_contra h
      have hr : i.val < r := by omega
      exact hi ⟨⟨i.val,hr⟩, Fin.ext rfl⟩
    refine ⟨⟨i.val-r, by omega⟩, ?_⟩
    apply Fin.ext
    change r+(i.val-r)=i.val
    omega
  · rintro ⟨j,hj⟩ ⟨l,hl⟩
    have h := congrArg Fin.val (hl.trans hj.symm)
    change l.val = r+j.val at h
    omega

private theorem rootProduct_firstBlock {R : Type*} [CommRing R] (r s : ℕ)
    (x : Fin (r+s) → R) :
    rootProduct x (fun _ => 1) (firstBlock r s).val =
      ∏ i : Fin r, (Polynomial.X - Polynomial.C (x (Fin.castAdd s i))) := by
  simp only [rootProduct, pow_one, firstBlock, Finset.prod_map, Fin.castAddEmb_apply]

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]

/-- The actual factor-identity quotient for the first r labelled roots. -/
abbrev BlockFactor (c : Collision.ChartData (r+s) r s A) :=
  FactorRing (c.f₁.map (algebraMap A (RootBase (r+s) A)))
    (c.f₂.map (algebraMap A (RootBase (r+s) A)))
    (baseRoot (r+s) A) (fun _ => 1) (firstBlock r s).val

/-- The quotient images of the original labelled roots. -/
def blockRoot (c : Collision.ChartData (r+s) r s A) (i : Fin (r+s)) : BlockFactor c :=
  Ideal.Quotient.mk _ (baseRoot (r+s) A i)

/-- The first ordered root block has exactly the first factor's polynomial. -/
theorem blockRoot_left_product (c : Collision.ChartData (r+s) r s A) :
    ∏ i : Fin r, (Polynomial.X - Polynomial.C (blockRoot c (Fin.castAdd s i))) =
      c.f₁.map (algebraMap A (BlockFactor c)) := by
  have h := ((factorIdeal_le_iff
    (c.f₁.map (algebraMap A (RootBase (r+s) A)))
    (c.f₂.map (algebraMap A (RootBase (r+s) A)))
    (baseRoot (r+s) A) (fun _ => 1) (firstBlock r s).val _).mp le_rfl).1
  rw [Polynomial.map_map, Ideal.Quotient.mk_comp_algebraMap, rootProduct_firstBlock] at h
  exact h

/-- The second ordered root block has exactly the second factor's polynomial. -/
theorem blockRoot_right_product (c : Collision.ChartData (r+s) r s A) :
    ∏ i : Fin s, (Polynomial.X - Polynomial.C (blockRoot c (Fin.natAdd r i))) =
      c.f₂.map (algebraMap A (BlockFactor c)) := by
  have h := ((factorIdeal_le_iff
    (c.f₁.map (algebraMap A (RootBase (r+s) A)))
    (c.f₂.map (algebraMap A (RootBase (r+s) A)))
    (baseRoot (r+s) A) (fun _ => 1) (firstBlock r s).val _).mp le_rfl).2
  rw [Polynomial.map_map, Ideal.Quotient.mk_comp_algebraMap, firstBlock_compl] at h
  simpa only [rootProduct, pow_one, Finset.prod_map,
    Function.Embedding.coeFn_mk, Fin.natAddEmb_apply, blockRoot] using h

/-- All quotient roots still multiply to the original universal polynomial. -/
theorem blockRoot_product (c : Collision.ChartData (r+s) r s A) :
    ∏ i : Fin (r+s), (Polynomial.X - Polynomial.C (blockRoot c i)) =
      (Collision.univPoly (r+s)).map (algebraMap (Depth.RB (r+s)) (BlockFactor c)) := by
  rw [Fin.prod_univ_add, blockRoot_left_product, blockRoot_right_product,
    ← Polynomial.map_mul, ← c.factor, Polynomial.map_map,
    ← IsScalarTower.algebraMap_eq (Depth.RB (r+s)) A (BlockFactor c)]

end KhanSL2.SymmetricFamily
