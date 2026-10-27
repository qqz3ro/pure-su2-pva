module

public import KhanSL2.Injectivity.SourceSectors
public import KhanSL2.SourceSupercommUngraded
public import Mathlib.Data.List.FinRange
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

@[expose] public section

/-! Symmetry of even monomials and alternation of odd monomials. -/

noncomputable section

namespace KhanSL2.Source

theorem xProduct_perm {xs ys : List ℕ} (h : xs.Perm ys) : xProduct xs = xProduct ys := by
  change (xs.map X).prod = (ys.map X).prod
  apply (h.map X).prod_eq'
  rw [List.pairwise_map]
  exact List.pairwise_of_forall (fun i j => X_mul_X i j)

theorem xProduct_ofFn_comp_perm {r : ℕ} (a : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    xProduct (List.ofFn (a ∘ σ)) = xProduct (List.ofFn a) :=
  xProduct_perm (σ.ofFn_comp_perm a)

theorem oddPart_sq (a : Source) : oddPart a * oddPart a = 0 := by
  have h := mul_oddPart (oddPart a) a
  rw [parity_oddPart, mul_neg] at h
  have htwo : (2 : ℂ) • (oddPart a * oddPart a) = 0 := by
    have hh : oddPart a * oddPart a + oddPart a * oddPart a = 0 := by
      calc
        oddPart a * oddPart a + oddPart a * oddPart a =
            -(oddPart a * oddPart a) + oddPart a * oddPart a :=
          congrArg (fun x => x + oddPart a * oddPart a) h
        _ = 0 := neg_add_cancel _
    simpa only [two_smul] using hh
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

def oddExteriorLift : ExteriorAlgebra ℂ Source →ₐ[ℂ] Source :=
  ExteriorAlgebra.lift ℂ ⟨oddPart, oddPart_sq⟩

def oddProduct (n : ℕ) : Source [⋀^Fin n]→ₗ[ℂ] Source :=
  oddExteriorLift.toLinearMap.compAlternatingMap (ExteriorAlgebra.ιMulti ℂ n)

theorem oddProduct_apply (n : ℕ) (a : Fin n → Source) :
    oddProduct n a = (List.ofFn fun i => oddPart (a i)).prod := by
  change oddExteriorLift (ExteriorAlgebra.ιMulti ℂ n a) = _
  rw [ExteriorAlgebra.ιMulti_apply, map_list_prod]
  simp [oddExteriorLift, List.map_ofFn, Function.comp_def]

theorem oddProduct_Y {s : ℕ} (a : Fin s → ℕ) :
    oddProduct s (Y ∘ a) = yProduct (List.ofFn a) := by
  rw [oddProduct_apply]
  simp [yProduct, List.map_ofFn, Function.comp_def]

theorem yProduct_ofFn_comp_perm {s : ℕ} (a : Fin s → ℕ) (σ : Equiv.Perm (Fin s)) :
    yProduct (List.ofFn (a ∘ σ)) = Equiv.Perm.sign σ • yProduct (List.ofFn a) := by
  rw [← oddProduct_Y, ← oddProduct_Y]
  exact (oddProduct s).map_perm (Y ∘ a) σ

theorem yProduct_ofFn_comp_swap {s : ℕ} (a : Fin s → ℕ) {i j : Fin s} (h : i ≠ j) :
    yProduct (List.ofFn (a ∘ Equiv.swap i j)) = -yProduct (List.ofFn a) := by
  rw [← oddProduct_Y, ← oddProduct_Y]
  exact (oddProduct s).map_swap (Y ∘ a) h

end KhanSL2.Source
