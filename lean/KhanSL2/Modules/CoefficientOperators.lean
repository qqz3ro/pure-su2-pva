module

public import KhanSL2.Modules.GradedAssembly

@[expose] public section

/-!
# Coefficient power-sum operators on the actual relative CE chains

Multiplication by `z^m` on the current algebra extends as a derivation to
`Λ(ε𝔤[z])`. On its degree-`B` part this is the action of the symmetric power
sum `t₁^m + ⋯ + t_B^m`: it shifts each coefficient factor in turn. These
operators commute with the current action and the relative CE boundary.
-/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.Modules

open Current LieChains

/-- Multiplication by `z^m` on `𝔤[z]`. -/
def coefficientShift (m : ℕ) : Module.End ℂ Cur :=
  LinearMap.rTensor MatrixSL2 (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ) ^ m))

@[simp] theorem coefficientShift_tmul (m : ℕ) (f : Polynomial ℂ) (x : MatrixSL2) :
    coefficientShift m (f ⊗ₜ[ℂ] x) = ((Polynomial.X ^ m) * f) ⊗ₜ[ℂ] x := rfl

@[simp] theorem coefficientShift_cur (m j : ℕ) (a : Fin 3) :
    coefficientShift m (cur j a) = cur (m + j) a := by
  simp only [cur, coefficientShift_tmul, pow_add]

/-- Loop multiplication commutes with every current adjoint action. -/
theorem coefficientShift_lie (m : ℕ) (x y : Cur) :
    coefficientShift m ⁅x, y⁆ = ⁅x, coefficientShift m y⁆ := by
  have h :
      (LieModule.toEnd ℂ Cur Cur : Cur →ₗ[ℂ] Module.End ℂ Cur).compr₂
          (coefficientShift m) =
        (LieModule.toEnd ℂ Cur Cur : Cur →ₗ[ℂ] Module.End ℂ Cur).compl₂
          (coefficientShift m) := by
    refine TensorProduct.ext' fun f a => TensorProduct.ext' fun g b => ?_
    change coefficientShift m ⁅f ⊗ₜ[ℂ] a, g ⊗ₜ[ℂ] b⁆ =
      ⁅f ⊗ₜ[ℂ] a, coefficientShift m (g ⊗ₜ[ℂ] b)⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, coefficientShift_tmul,
      coefficientShift_tmul, LieAlgebra.ExtendScalars.bracket_tmul]
    rw [show (Polynomial.X ^ m) * (f * g) = f * ((Polynomial.X ^ m) * g) by ring]
  exact congrArg (fun F => F x y) h

theorem coefficientShift_commute (m n : ℕ) :
    Commute (coefficientShift m) (coefficientShift n) := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul f x =>
    change ((Polynomial.X ^ m) * ((Polynomial.X ^ n) * f)) ⊗ₜ[ℂ] x =
      ((Polynomial.X ^ n) * ((Polynomial.X ^ m) * f)) ⊗ₜ[ℂ] x
    congr 1
    ring
  | add x y hx hy =>
    simp only [Module.End.mul_apply, map_add, hx, hy]

/-- Derivation extension preserves commuting endomorphisms. -/
theorem derivExt_commute {M : Type*} [AddCommGroup M] [Module ℂ M]
    {D E : Module.End ℂ M} (h : Commute D E) :
    Commute (derivExt D) (derivExt E) := by
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  change derivExt D (derivExt E v) - derivExt E (derivExt D v) = 0
  rw [derivExt_commutator, h.eq, sub_self, derivExt_zero_apply]

/-- The power sum acts by shifting each coefficient factor and summing. -/
def coefficientPower (m : ℕ) : Module.End ℂ NB := derivExt (coefficientShift m)

@[simp] theorem coefficientPower_one (m : ℕ) : coefficientPower m 1 = 0 :=
  derivExt_one _

@[simp] theorem coefficientPower_generator (m j : ℕ) (a : Fin 3) :
    coefficientPower m (ExteriorAlgebra.ι ℂ (cur j a)) =
      ExteriorAlgebra.ι ℂ (cur (m + j) a) := by
  simp [coefficientPower]

theorem coefficientPower_mul (m : ℕ) (u v : NB) :
    coefficientPower m (u * v) = coefficientPower m u * v + u * coefficientPower m v :=
  derivExt_mul _ _ _

theorem coefficientPower_commute (m n : ℕ) :
    Commute (coefficientPower m) (coefficientPower n) :=
  derivExt_commute (coefficientShift_commute m n)

/-- Every coefficient power sum is a current-module endomorphism. -/
theorem coefficientPower_lie (m : ℕ) (x : Cur) (v : NB) :
    coefficientPower m ⁅x, v⁆ = ⁅x, coefficientPower m v⁆ := by
  have h : Commute (coefficientShift m) (adCur x) := by
    apply LinearMap.ext
    intro y
    exact coefficientShift_lie m x y
  exact LinearMap.congr_fun (derivExt_commute h).eq v

/-- The operator on actual CE chains, acting only on the coefficient factor. -/
def coefficientChainPower (m : ℕ) : Module.End ℂ GenChains :=
  LinearMap.lTensor (ExteriorAlgebra ℂ plus) (coefficientPower m)

@[simp] theorem coefficientChainPower_tmul (m : ℕ)
    (u : ExteriorAlgebra ℂ plus) (v : NB) :
    coefficientChainPower m (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] coefficientPower m v := rfl

theorem coefficientChainPower_eq_lieDeriv (m : ℕ) :
    coefficientChainPower m = lieDeriv (0 : Module.End ℂ plus) (coefficientPower m) := by
  apply TensorProduct.ext'
  intro u v
  simp [coefficientChainPower_tmul, lieDeriv_tmul, derivExt_zero_apply]

theorem coefficientPower_compatible (m : ℕ) :
    IsCompatibleDerivation (0 : Module.End ℂ plus) (coefficientPower m) where
  derivation y z := by simp
  compatible y v := by
    simp only [LinearMap.zero_apply, zero_lie, zero_add]
    exact coefficientPower_lie m (y : Cur) v

/-- Power sums commute with the independently defined CE boundary. -/
theorem boundary_coefficientChainPower (m : ℕ) (ξ : GenChains) :
    LieChains.boundary NB (coefficientChainPower m ξ) =
      coefficientChainPower m (LieChains.boundary NB ξ) := by
  rw [coefficientChainPower_eq_lieDeriv]
  exact boundary_lieDeriv (coefficientPower_compatible m) ξ

/-- Commutation on chains follows from commutation on coefficients. -/
theorem coefficientChainPower_lieDeriv (m : ℕ) (D : Module.End ℂ plus)
    (E : Module.End ℂ NB) (hE : Commute (coefficientPower m) E) (ξ : GenChains) :
    coefficientChainPower m (lieDeriv D E ξ) =
      lieDeriv D E (coefficientChainPower m ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [lieDeriv_tmul, map_add, coefficientChainPower_tmul]
    rw [show coefficientPower m (E v) = E (coefficientPower m v) from
      LinearMap.congr_fun hE.eq v]
  | add ξ η hξ hη => simp only [map_add, hξ, hη]

/-- The coefficient action also respects the constant `sl₂` relations. -/
theorem coefficientChainPower_relTheta (m : ℕ) (a : Fin 3) (ξ : GenChains) :
    coefficientChainPower m (relTheta a ξ) = relTheta a (coefficientChainPower m ξ) := by
  apply coefficientChainPower_lieDeriv
  apply LinearMap.ext
  intro v
  exact coefficientPower_lie m (cur 0 a) v

theorem coefficientChainPower_commute (m n : ℕ) :
    Commute (coefficientChainPower m) (coefficientChainPower n) := by
  apply TensorProduct.ext'
  intro u v
  change u ⊗ₜ[ℂ] coefficientPower m (coefficientPower n v) =
    u ⊗ₜ[ℂ] coefficientPower n (coefficientPower m v)
  exact congrArg (fun w => u ⊗ₜ[ℂ] w)
    (LinearMap.congr_fun (coefficientPower_commute m n).eq v)

/-- The action preserves the relative relation subspace. -/
theorem coefficientChainPower_mem_relations (m : ℕ) {ξ : GenChains}
    (hξ : ξ ∈ genRelations) : coefficientChainPower m ξ ∈ genRelations := by
  have h : genRelations ≤ genRelations.comap (coefficientChainPower m) := by
    apply iSup_le
    rintro a _ ⟨η, rfl⟩
    change coefficientChainPower m (relTheta a η) ∈ genRelations
    rw [coefficientChainPower_relTheta]
    exact Submodule.mem_iSup_of_mem a ⟨_, rfl⟩
  exact h hξ

/-- The resulting operator on actual relative chains. -/
def coefficientRelPower (m : ℕ) : Module.End ℂ RelChains :=
  genRelations.mapQ genRelations (coefficientChainPower m)
    (fun _ h => coefficientChainPower_mem_relations m h)

@[simp] theorem coefficientRelPower_mk (m : ℕ) (ξ : GenChains) :
    coefficientRelPower m (genRelations.mkQ ξ) =
      genRelations.mkQ (coefficientChainPower m ξ) := rfl

theorem relBoundary_coefficientRelPower (m : ℕ) (x : RelChains) :
    relBoundary (coefficientRelPower m x) = coefficientRelPower m (relBoundary x) := by
  obtain ⟨ξ, rfl⟩ := genRelations.mkQ_surjective x
  simp only [coefficientRelPower_mk, relBoundary_mk, boundary_coefficientChainPower]

theorem coefficientRelPower_commute (m n : ℕ) :
    Commute (coefficientRelPower m) (coefficientRelPower n) := by
  apply LinearMap.ext
  intro x
  obtain ⟨ξ, rfl⟩ := genRelations.mkQ_surjective x
  change genRelations.mkQ (coefficientChainPower m (coefficientChainPower n ξ)) =
    genRelations.mkQ (coefficientChainPower n (coefficientChainPower m ξ))
  exact congrArg genRelations.mkQ
    (LinearMap.congr_fun (coefficientChainPower_commute m n).eq ξ)

end KhanSL2.Modules
