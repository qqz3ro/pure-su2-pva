module

public import KhanSL2.ColorBasis
public import KhanSL2.CE
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

/-!
# The current algebra `𝔩 = 𝔤[z]` and its ideal `𝔩₊ = z 𝔤[z]`

`Cur` is `ℂ[z] ⊗ sl₂` with Mathlib's base-change Lie algebra structure.
`cur n a = zⁿ ⊗ t_a` in the color basis. The ideal `plus` is the kernel of
evaluation at `z = 0`; it has the basis `cur (j+1) a`.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open MatrixSL2

/-- The current algebra `𝔤[z]`. -/
abbrev Cur := Polynomial ℂ ⊗[ℂ] MatrixSL2

/-- The color basis of `sl₂`. -/
def colorBasis : Module.Basis (Fin 3) ℂ MatrixSL2 := (Pi.basisFun ℂ (Fin 3)).map colorEquiv

@[simp] theorem colorBasis_apply (a : Fin 3) : colorBasis a = color a := by
  simp [colorBasis, colorEquiv_apply, Pi.single_apply]

/-- `cur n a = zⁿ ⊗ t_a`. -/
def cur (n : ℕ) (a : Fin 3) : Cur := (Polynomial.X ^ n) ⊗ₜ[ℂ] color a

/-- The monomial basis of `𝔤[z]`. -/
def curBasis : Module.Basis (ℕ × Fin 3) ℂ Cur :=
  (Polynomial.basisMonomials ℂ).tensorProduct colorBasis

@[simp] theorem curBasis_apply (n : ℕ) (a : Fin 3) : curBasis (n, a) = cur n a := by
  simp [curBasis, cur, Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial]

theorem curBasis_apply' (p : ℕ × Fin 3) : curBasis p = cur p.1 p.2 := curBasis_apply p.1 p.2

theorem lie_cur_cur (i j : ℕ) (a b : Fin 3) :
    ⁅cur i a, cur j b⁆ = ∑ c : Fin 3, epsilon a b c • cur (i + j) c := by
  rw [cur, cur, LieAlgebra.ExtendScalars.bracket_tmul, color_bracket, ← pow_add]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, cur]

/-! ## Evaluation at zero -/

/-- The coefficient of `z⁰`. -/
def coeffZero : Cur →ₗ[ℂ] MatrixSL2 :=
  TensorProduct.lift ((LinearMap.lsmul ℂ MatrixSL2) ∘ₗ Polynomial.lcoeff ℂ 0)

@[simp] theorem coeffZero_tmul (p : Polynomial ℂ) (x : MatrixSL2) :
    coeffZero (p ⊗ₜ x) = p.coeff 0 • x := rfl

@[simp] theorem coeffZero_cur (n : ℕ) (a : Fin 3) :
    coeffZero (cur n a) = if n = 0 then color a else 0 := by
  rw [cur, coeffZero_tmul, Polynomial.coeff_X_pow]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

theorem coeffZero_lie (f g : Cur) : coeffZero ⁅f, g⁆ = ⁅coeffZero f, coeffZero g⁆ := by
  have key : (LieModule.toEnd ℂ Cur Cur : Cur →ₗ[ℂ] Module.End ℂ Cur).compr₂ coeffZero =
      (LieModule.toEnd ℂ MatrixSL2 MatrixSL2 : MatrixSL2 →ₗ[ℂ] Module.End ℂ MatrixSL2).compl₁₂
        coeffZero coeffZero := by
    refine TensorProduct.ext' fun p x => TensorProduct.ext' fun r y => ?_
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LieModule.toEnd_apply_apply]
    change coeffZero ⁅p ⊗ₜ[ℂ] x, r ⊗ₜ[ℂ] y⁆ = _
    rw [LieAlgebra.ExtendScalars.bracket_tmul, coeffZero_tmul, coeffZero_tmul,
      coeffZero_tmul, Polynomial.mul_coeff_zero]
    change _ = ⁅p.coeff 0 • x, r.coeff 0 • y⁆
    rw [smul_lie, lie_smul, smul_smul, mul_comm]
  exact congrArg (fun F => F f g) key

/-- The ideal `𝔩₊ = z 𝔤[z]`: the kernel of evaluation at `z = 0`. -/
def plus : LieIdeal ℂ Cur :=
  { LinearMap.ker coeffZero with
    lie_mem := by
      intro f g hg
      change coeffZero ⁅f, g⁆ = 0
      rw [coeffZero_lie]
      change coeffZero g = 0 at hg
      rw [hg, lie_zero] }

theorem mem_plus {f : Cur} : f ∈ plus ↔ coeffZero f = 0 := Iff.rfl

theorem cur_succ_mem_plus (j : ℕ) (a : Fin 3) : cur (j + 1) a ∈ plus := by
  rw [mem_plus, coeffZero_cur]; simp

/-- The basis element `cur (j+1) a` of `𝔩₊`. -/
def plusCur (j : ℕ) (a : Fin 3) : plus := ⟨cur (j + 1) a, cur_succ_mem_plus j a⟩

theorem plusCur_linearIndependent :
    LinearIndependent ℂ (fun p : ℕ × Fin 3 => plusCur p.1 p.2) := by
  apply LinearIndependent.of_comp (plus : Submodule ℂ Cur).subtype
  have h : (plus : Submodule ℂ Cur).subtype ∘ (fun p : ℕ × Fin 3 => plusCur p.1 p.2) =
      curBasis ∘ (fun p : ℕ × Fin 3 => (p.1 + 1, p.2)) := by
    funext p
    simp only [Function.comp_apply, Submodule.subtype_apply, curBasis_apply']
    rfl
  rw [h]
  exact curBasis.linearIndependent.comp _ (fun p q h => by
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff] at h
    exact Prod.ext h.1 h.2)

/-- Evaluation at zero in the monomial basis. -/
theorem coeffZero_eq_sum_repr (f : Cur) :
    coeffZero f = ∑ b : Fin 3, curBasis.repr f (0, b) • color b := by
  have hlin : coeffZero = ∑ b : Fin 3,
      (LinearMap.smulRight ((Finsupp.lapply (0, b)) ∘ₗ curBasis.repr.toLinearMap) (color b)) := by
    apply curBasis.ext
    rintro ⟨n, a⟩
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Module.Basis.repr_self, Finsupp.lapply_apply, Finsupp.single_apply, Prod.mk.injEq]
    rw [curBasis_apply, coeffZero_cur]
    by_cases hn : n = 0
    · subst hn
      simp [Finset.sum_ite_eq']
    · simp [hn, Ne.symm hn]
  rw [hlin]
  simp

theorem cur_repr_zero_of_mem_plus {f : Cur} (hf : f ∈ plus) (a : Fin 3) :
    curBasis.repr f (0, a) = 0 := by
  have h := coeffZero_eq_sum_repr f
  rw [mem_plus.mp hf] at h
  have h' : ∑ b : Fin 3, curBasis.repr f (0, b) • colorBasis b = 0 := by
    simpa using h.symm
  have := Fintype.linearIndependent_iff.mp colorBasis.linearIndependent _ h'
  exact this a

theorem plusCur_span : ⊤ ≤ Submodule.span ℂ (Set.range fun p : ℕ × Fin 3 => plusCur p.1 p.2) := by
  rintro x -
  have hsum : (x : Cur) = ∑ p ∈ (curBasis.repr x).support, curBasis.repr x p • cur p.1 p.2 := by
    conv_lhs => rw [← curBasis.linearCombination_repr (x : Cur)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [curBasis_apply']
  have hx : x = ∑ p ∈ (curBasis.repr x).support,
      curBasis.repr x p • plusCur (p.1 - 1) p.2 := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [hsum]
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : p.1 ≠ 0 := by
      intro h0
      have := cur_repr_zero_of_mem_plus x.property p.2
      rw [Finsupp.mem_support_iff] at hp
      apply hp
      rw [← this]
      congr 1
      exact Prod.ext h0 rfl
    simp only [Submodule.coe_smul, plusCur]
    congr 2
    omega
  rw [hx]
  apply Submodule.sum_mem
  intro p _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p.1 - 1, p.2), rfl⟩)

/-- The basis `z^(j+1) ⊗ t_a` of `𝔩₊`. -/
def plusBasis : Module.Basis (ℕ × Fin 3) ℂ plus :=
  Module.Basis.mk plusCur_linearIndependent plusCur_span

@[simp] theorem plusBasis_apply (j : ℕ) (a : Fin 3) : plusBasis (j, a) = plusCur j a := by
  simp [plusBasis]

end KhanSL2.Current
