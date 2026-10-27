module

public import KhanSL2.Chains.CurrentModel
public import KhanSL2.Chains.Coinvariant
public import KhanSL2.LieChains.Basic
public import KhanSL2.CELeibniz
public import KhanSL2.ExteriorSupercomm
public import KhanSL2.ExteriorContraction

@[expose] public section

/-!
# Setup for comparing general and concrete chains

* `NB = Λ(ε𝔩)`, the exterior algebra of `𝔩 = 𝔤[z]`, is an `𝔩`-module through
  derivations: `x · ν = derivExt (ad x) ν`. Its degree-`B` part is `N_B`.
* `GenChains = Λ𝔩₊ ⊗ NB` are the CE chains of `𝔩₊` with coefficients in `NB`.
* `Phi : GenChains → Chain` sends `z^(j+1) ⊗ t_a ∈ 𝔩₊` to the generator `c_j^a`
  and `z^j ⊗ t_a ∈ ε𝔩` to `b_j^a`, multiplicatively.
* `iotaC`, `iotaB` are the contractions adjoint to exterior multiplication by
  those generators.
-/

noncomputable section

open scoped TensorProduct

namespace KhanSL2.Current

open LieChains FiniteExterior

/-! ## The coefficient module `Λ(ε𝔩)` -/

/-- The adjoint action of `𝔩` on itself. -/
abbrev adCur (y : Cur) : Module.End ℂ Cur := LieModule.toEnd ℂ Cur Cur y

/-- `Λ(ε𝔩)`. -/
abbrev NB := ExteriorAlgebra ℂ Cur

instance : LieRingModule Cur NB where
  bracket y ν := derivExt (adCur y) ν
  add_lie y z ν := by
    change derivExt (adCur (y + z)) ν = derivExt (adCur y) ν + derivExt (adCur z) ν
    rw [adCur, map_add, derivExt_add]
  lie_add y ν ν' := map_add _ _ _
  leibniz_lie y z ν := by
    change derivExt (adCur y) (derivExt (adCur z) ν) =
      derivExt (adCur ⁅y, z⁆) ν + derivExt (adCur z) (derivExt (adCur y) ν)
    have hlie : adCur ⁅y, z⁆ = adCur y * adCur z - adCur z * adCur y := by
      refine LinearMap.ext fun w => ?_
      rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
      exact (eq_sub_of_add_eq (LieRingModule.leibniz_lie y z w).symm)
    have h := derivExt_commutator (adCur y) (adCur z) ν
    rw [hlie, ← h]
    abel

instance : LieModule ℂ Cur NB where
  smul_lie c y ν := by
    change derivExt (adCur (c • y)) ν = c • derivExt (adCur y) ν
    rw [adCur, map_smul, derivExt_smul]
  lie_smul c y ν := map_smul _ _ _

theorem lie_NB (y : Cur) (ν : NB) : ⁅y, ν⁆ = derivExt (adCur y) ν := rfl

theorem toEnd_NB (y : Cur) : LieModule.toEnd ℂ Cur NB y = derivExt (adCur y) := rfl

/-- The CE chains of `𝔩₊` with coefficients in `Λ(ε𝔩)`. -/
abbrev GenChains := Chains ℂ plus NB

/-! ## The relative action of `𝔤` -/

/-- `t_a` acting on `𝔩₊`. -/
def relD (a : Fin 3) : Module.End ℂ plus := LieModule.toEnd ℂ Cur plus (cur 0 a)

/-- `t_a` acting on `Λ(ε𝔩)`. -/
def relS (a : Fin 3) : Module.End ℂ NB := LieModule.toEnd ℂ Cur NB (cur 0 a)

/-- The action of `t_a ∈ 𝔤` on the chains. -/
def relTheta (a : Fin 3) : Module.End ℂ GenChains := lieDeriv (relD a) (relS a)

theorem relTheta_compatible (a : Fin 3) : IsCompatibleDerivation (relD a) (relS a) where
  derivation y z := by
    apply Subtype.ext
    simp only [relD, LieModule.toEnd_apply_apply, LieSubmodule.coe_bracket]
    exact LieRingModule.leibniz_lie (cur 0 a) (y : Cur) (z : Cur)
  compatible y m := by
    simp only [relS, relD, LieModule.toEnd_apply_apply, LieIdeal.coe_bracket_of_module,
      LieSubmodule.coe_bracket]
    exact LieRingModule.leibniz_lie (cur 0 a) (y : Cur) m

/-! ## The comparison map -/

/-- `z^(j+1) ⊗ t_a ↦ c_j^a`. -/
def phiC : plus →ₗ[ℂ] Chain := plusBasis.constr ℂ fun p => generator (Mode.c p.1 p.2)

/-- `z^j ⊗ t_a ↦ b_j^a`. -/
def phiB : Cur →ₗ[ℂ] Chain := curBasis.constr ℂ fun p => generator (Mode.b p.1 p.2)

@[simp] theorem phiC_plusCur (j : ℕ) (a : Fin 3) : phiC (plusCur j a) = generator (Mode.c j a) := by
  rw [← plusBasis_apply, phiC, Module.Basis.constr_basis]

@[simp] theorem phiB_cur (n : ℕ) (a : Fin 3) : phiB (cur n a) = generator (Mode.b n a) := by
  rw [← curBasis_apply, phiB, Module.Basis.constr_basis]

/-- The span of the generators: cochains (or chains) of exterior degree one. -/
def degOne : Submodule ℂ Cochain := Finsupp.supported ℂ ℂ {s : ExteriorMonomial | s.card = 1}

theorem generator_mem_degOne (m : Mode) : generator m ∈ degOne := by
  rw [degOne, generator]
  exact Finsupp.single_mem_supported ℂ 1 (by simp)

theorem phiC_mem (y : plus) : phiC y ∈ degOne := by
  rw [phiC, Module.Basis.constr_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun p _ => Submodule.smul_mem _ _ (generator_mem_degOne _)

theorem phiB_mem (y : Cur) : phiB y ∈ degOne := by
  rw [phiB, Module.Basis.constr_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun p _ => Submodule.smul_mem _ _ (generator_mem_degOne _)

theorem parity_of_mem_degOne {v : Cochain} (hv : v ∈ degOne) : cochainParity v = -v := by
  rw [degOne, Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, hs, rfl⟩ := hw
    rw [cochainParity_apply]
    simp [hs.out]
  | zero => simp
  | add v w _ _ hv hw => rw [map_add, hv, hw, neg_add]
  | smul r v _ hv => rw [map_smul, hv, smul_neg]

theorem mul_self_of_mem_degOne {v : Cochain} (hv : v ∈ degOne) : v * v = 0 := by
  have h := wedge_comm_of_parity_odd GeneratorOrder.code GeneratorOrder.code_injective v
    (parity_of_mem_degOne hv) v
  change FiniteExterior.wedge _ v v = _ at h
  have hp : FiniteExterior.parityLinear v = -v := by
    rw [← cochainParity_apply]; exact parity_of_mem_degOne hv
  rw [hp] at h
  change FiniteExterior.wedge _ v v = (FiniteExterior.wedgeLinear GeneratorOrder.code v) (-v) at h
  rw [show (FiniteExterior.wedgeLinear GeneratorOrder.code v) (-v) =
    -(FiniteExterior.wedgeLinear GeneratorOrder.code v v) from map_neg _ _] at h
  have h' : FiniteExterior.wedgeLinear GeneratorOrder.code v v =
      -(FiniteExterior.wedgeLinear GeneratorOrder.code v v) := h
  have h2 : (2 : ℂ) • FiniteExterior.wedgeLinear GeneratorOrder.code v v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h']
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- `Λ𝔩₊ → Chain`, multiplicatively. -/
def PhiC : ExteriorAlgebra ℂ plus →ₐ[ℂ] Chain :=
  ExteriorAlgebra.lift ℂ ⟨phiC, fun y => mul_self_of_mem_degOne (phiC_mem y)⟩

/-- `Λ(ε𝔩) → Chain`, multiplicatively. -/
def PhiB : NB →ₐ[ℂ] Chain :=
  ExteriorAlgebra.lift ℂ ⟨phiB, fun y => mul_self_of_mem_degOne (phiB_mem y)⟩

@[simp] theorem PhiC_ι (y : plus) : PhiC (ExteriorAlgebra.ι ℂ y) = phiC y :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

@[simp] theorem PhiB_ι (y : Cur) : PhiB (ExteriorAlgebra.ι ℂ y) = phiB y :=
  ExteriorAlgebra.lift_ι_apply _ _ _ _

/-- The comparison map `Λ𝔩₊ ⊗ Λ(ε𝔩) → Chain`, `ω ⊗ ν ↦ Φ(ω) Φ(ν)`. -/
def Phi : GenChains →ₗ[ℂ] Chain :=
  TensorProduct.lift ((LinearMap.mul ℂ Chain).compl₁₂ PhiC.toLinearMap PhiB.toLinearMap)

@[simp] theorem Phi_tmul (ω : ExteriorAlgebra ℂ plus) (ν : NB) :
    Phi (ω ⊗ₜ ν) = PhiC ω * PhiB ν := rfl

theorem Phi_one_tmul (ν : NB) : Phi ((1 : ExteriorAlgebra ℂ plus) ⊗ₜ ν) = PhiB ν := by
  simp

theorem Phi_wedgeLeft (y : plus) (ξ : GenChains) :
    Phi (wedgeLeft NB y ξ) = phiC y * Phi ξ := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul ω ν => simp [mul_assoc]
  | add ξ η hξ hη => simp only [map_add, hξ, hη, mul_add]

/-! ## Contractions -/

/-- Removal of the generator `m`. -/
abbrev ctr (m : Mode) : Module.End ℂ Cochain := contraction GeneratorOrder.code m

/-- Contraction adjoint to `phiC y * ·`. -/
def iotaC : plus →ₗ[ℂ] Module.End ℂ Cochain := plusBasis.constr ℂ fun p => ctr (Mode.c p.1 p.2)

/-- Contraction adjoint to `phiB y * ·`. -/
def iotaB : Cur →ₗ[ℂ] Module.End ℂ Cochain := curBasis.constr ℂ fun p => ctr (Mode.b p.1 p.2)

@[simp] theorem iotaC_plusCur (j : ℕ) (a : Fin 3) : iotaC (plusCur j a) = ctr (Mode.c j a) := by
  rw [← plusBasis_apply, iotaC, Module.Basis.constr_basis]

@[simp] theorem iotaB_cur (n : ℕ) (a : Fin 3) : iotaB (cur n a) = ctr (Mode.b n a) := by
  rw [← curBasis_apply, iotaB, Module.Basis.constr_basis]

theorem pairing_ctr (m : Mode) (u : Cochain) (ζ : Chain) :
    pairing (ctr m u) ζ = pairing u (generator m * ζ) :=
  coefficientPairing_contraction m u ζ

theorem pairing_iotaC (y : plus) (u : Cochain) (ζ : Chain) :
    pairing (iotaC y u) ζ = pairing u (phiC y * ζ) := by
  have h : ((pairing.flip ζ) ∘ₗ (LinearMap.applyₗ u) ∘ₗ iotaC) =
      ((pairing u) ∘ₗ (LinearMap.mulRight ℂ ζ) ∘ₗ phiC) := by
    apply plusBasis.ext
    rintro ⟨j, a⟩
    simp [pairing_ctr]
  exact congrArg (fun F => F y) h

theorem pairing_iotaB (y : Cur) (u : Cochain) (ζ : Chain) :
    pairing (iotaB y u) ζ = pairing u (phiB y * ζ) := by
  have h : ((pairing.flip ζ) ∘ₗ (LinearMap.applyₗ u) ∘ₗ iotaB) =
      ((pairing u) ∘ₗ (LinearMap.mulRight ℂ ζ) ∘ₗ phiB) := by
    apply curBasis.ext
    rintro ⟨n, a⟩
    simp [pairing_ctr]
  exact congrArg (fun F => F y) h

end KhanSL2.Current
