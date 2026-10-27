module

public import KhanSL2.Deformation.Sl2Casimir

@[expose] public section

/-!
# Reduction to invariants by a Casimir null-homotopy

Let `D` be a differential raising a grading `W n` by one, `L₀, L₁, L₂` an `𝔰𝔩₂` action commuting
with `D`, and `ι_a` operators lowering the grading with the Cartan formula
`D ι_a + ι_a D = L_a`. Then the Casimir `Ω = Σ L_a²` is null-homotopic:
`Ω = D h + h D` with `h = Σ ι_a L_a`. On finite-dimensional pieces `Ω` splits into kernel
(the `L`-invariants) and range, and on the range `D` is exact.

`casimir_reduction`: inside the subspace `S` cut out by operators `M_j` commuting with
everything, a `D`-cocycle `u ∈ S ∩ W n` is `u₀ + D w` with `u₀ ∈ S ∩ W n` an `L`-invariant
`D`-cocycle and `w ∈ S ∩ W (n - 1)`.
-/

noncomputable section

namespace KhanSL2.Deformation

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Graded finite-dimensional pieces with an `𝔰𝔩₂` action. -/
structure CasimirSplit (V : Type*) [AddCommGroup V] [Module ℂ V] where
  W : ℤ → Submodule ℂ V
  fin : ∀ n, FiniteDimensional ℂ (W n)
  L : Fin 3 → V →ₗ[ℂ] V
  L_mem : ∀ a {n v}, v ∈ W n → L a v ∈ W n
  action : IsColorAction L

namespace CasimirSplit

variable (C : CasimirSplit V)

/-- The Casimir `Ω = Σ L_a²`. -/
def Ω : V →ₗ[ℂ] V := colorCasimir C.L

theorem Ω_apply (v : V) : C.Ω v = ∑ a : Fin 3, C.L a (C.L a v) := by
  simp [Ω, colorCasimir, LinearMap.sum_apply, Module.End.mul_apply]

theorem Ω_mem {n : ℤ} {v : V} (hv : v ∈ C.W n) : C.Ω v ∈ C.W n := by
  rw [Ω_apply]
  exact Submodule.sum_mem _ fun a _ => C.L_mem a (C.L_mem a hv)

/-- Restriction of the action to a piece. -/
def Lr (n : ℤ) : Fin 3 → Module.End ℂ (C.W n) :=
  restrictL C.L (C.W n) (fun a _ hv => C.L_mem a hv)

theorem Ω_restrict (n : ℤ) (v : C.W n) : (colorCasimir (C.Lr n) v : V) = C.Ω v :=
  colorCasimir_restrict _ _ _ v

/-- Splitting a piece into the kernel and the range of `Ω`. -/
theorem exists_split {n : ℤ} {u : V} (hu : u ∈ C.W n) :
    ∃ u₀ ∈ C.W n, C.Ω u₀ = 0 ∧ ∃ v ∈ C.W n, u = u₀ + C.Ω v := by
  have := C.fin n
  have hc := casimir_isCompl (C.Lr n) (C.action.restrict (C.W n) (fun a _ hv => C.L_mem a hv))
  have hmem : (⟨u, hu⟩ : C.W n) ∈ LinearMap.ker (colorCasimir (C.Lr n)) ⊔
      LinearMap.range (colorCasimir (C.Lr n)) := by rw [hc.sup_eq_top]; trivial
  obtain ⟨y, hy, z, ⟨x, rfl⟩, hyz⟩ := Submodule.mem_sup.mp hmem
  refine ⟨y, y.property, ?_, x, x.property, ?_⟩
  · have := congrArg Subtype.val (LinearMap.mem_ker.mp hy)
    rwa [Ω_restrict] at this
  · have := congrArg Subtype.val hyz
    simp only [Submodule.coe_add] at this
    rw [← this, Ω_restrict]

/-- An element in both the kernel and the range of `Ω` (on a piece) is zero. -/
theorem eq_zero_of_ker_range {n : ℤ} {y : V} (hy : y ∈ C.W n) (hΩ : C.Ω y = 0) {x : V}
    (hx : x ∈ C.W n) (hxy : C.Ω x = y) : y = 0 := by
  have := C.fin n
  have hc := casimir_isCompl (C.Lr n) (C.action.restrict (C.W n) (fun a _ hv => C.L_mem a hv))
  have hker : (⟨y, hy⟩ : C.W n) ∈ LinearMap.ker (colorCasimir (C.Lr n)) := by
    apply Subtype.ext; rw [Ω_restrict]; exact hΩ
  have hran : (⟨y, hy⟩ : C.W n) ∈ LinearMap.range (colorCasimir (C.Lr n)) :=
    ⟨⟨x, hx⟩, by apply Subtype.ext; rw [Ω_restrict]; exact hxy⟩
  have := Submodule.disjoint_def.mp hc.disjoint _ hker hran
  exact congrArg Subtype.val this

/-- `Ω`-kernel elements are invariant. -/
theorem L_eq_zero_of_Ω {n : ℤ} {y : V} (hy : y ∈ C.W n) (hΩ : C.Ω y = 0) (a : Fin 3) :
    C.L a y = 0 := by
  have := C.fin n
  have h := casimir_ker (C.Lr n) (C.action.restrict (C.W n) (fun a _ hv => C.L_mem a hv))
    (v := ⟨y, hy⟩) (by apply Subtype.ext; rw [Ω_restrict]; exact hΩ) a
  exact congrArg Subtype.val h

/-- **Invariant preimages.** If `u = E w` with `E` commuting with `Ω`, `w` in a piece and in the
common kernel of operators `M_j` commuting with `Ω`, and `u` is `Ω`-invariant, then `u = E w₀`
with `w₀` additionally in the kernel of `Ω`. -/
theorem exists_ker_preimage {J : Type*} (M : J → V →ₗ[ℂ] V)
    (M_mem : ∀ j {n v}, v ∈ C.W n → M j v ∈ C.W n)
    (M_Ω : ∀ j v, M j (C.Ω v) = C.Ω (M j v))
    (E : V →ₗ[ℂ] V) {n m : ℤ} (E_mem : ∀ {v}, v ∈ C.W n → E v ∈ C.W m)
    (E_Ω : ∀ v, E (C.Ω v) = C.Ω (E v))
    {w : V} (hw : w ∈ C.W n) (hMw : ∀ j, M j w = 0) (hΩ : C.Ω (E w) = 0) :
    ∃ w₀ ∈ C.W n, C.Ω w₀ = 0 ∧ (∀ j, M j w₀ = 0) ∧ E w₀ = E w := by
  obtain ⟨w₀, hw₀, hΩ₀, x, hx, hwx⟩ := C.exists_split hw
  have hEx : E (C.Ω x) = 0 := by
    have h1 : C.Ω (E w) = C.Ω (E w₀) + C.Ω (E (C.Ω x)) := by rw [hwx, map_add, map_add]
    have h2 : C.Ω (E w₀) = 0 := by rw [← E_Ω, hΩ₀, map_zero]
    rw [h2, zero_add, hΩ] at h1
    exact C.eq_zero_of_ker_range (E_mem (C.Ω_mem hx)) h1.symm (E_mem hx) (E_Ω x).symm
  have hM (j : J) : M j w₀ = 0 := by
    have hsum : M j w₀ + M j (C.Ω x) = 0 := by rw [← map_add, ← hwx]; exact hMw j
    apply C.eq_zero_of_ker_range (M_mem j hw₀) (by rw [← M_Ω, hΩ₀, map_zero])
      (x := -M j x) (Submodule.neg_mem _ (M_mem j hx))
    rw [map_neg, ← M_Ω]
    exact (eq_neg_of_add_eq_zero_left hsum).symm
  exact ⟨w₀, hw₀, hΩ₀, hM, by rw [hwx, map_add, hEx, add_zero]⟩

end CasimirSplit

/-- The data of a Casimir null-homotopy. -/
structure CasimirHomotopy (V : Type*) [AddCommGroup V] [Module ℂ V] extends CasimirSplit V where
  D : V →ₗ[ℂ] V
  ι : Fin 3 → V →ₗ[ℂ] V
  D_mem : ∀ {n v}, v ∈ W n → D v ∈ W (n + 1)
  ι_mem : ∀ a {n v}, v ∈ W n → ι a v ∈ W (n - 1)
  cartan : ∀ a v, D (ι a v) + ι a (D v) = L a v
  D_L : ∀ a v, D (L a v) = L a (D v)

namespace CasimirHomotopy

variable (C : CasimirHomotopy V)

/-- The homotopy `h = Σ ι_a L_a`. -/
def h : V →ₗ[ℂ] V := ∑ a : Fin 3, C.ι a ∘ₗ C.L a

theorem Ω_eq (v : V) : C.Ω v = C.D (C.h v) + C.h (C.D v) := by
  simp only [CasimirSplit.Ω_apply, h, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    ← C.D_L, ← Finset.sum_add_distrib, C.cartan]

theorem h_mem {n : ℤ} {v : V} (hv : v ∈ C.W n) : C.h v ∈ C.W (n - 1) := by
  simp only [h, LinearMap.sum_apply, LinearMap.comp_apply]
  exact Submodule.sum_mem _ fun a _ => C.ι_mem a (C.L_mem a hv)

theorem D_Ω (v : V) : C.D (C.Ω v) = C.Ω (C.D v) := by
  simp only [CasimirSplit.Ω_apply, map_sum, C.D_L]

/-- **Casimir reduction.** Let `M_j` be operators preserving the pieces and commuting with `Ω` and
with `h`. On `S = ⋂ ker M_j`, every `D`-cocycle is an `L`-invariant `D`-cocycle plus a
`D`-boundary, all within `S`. -/
theorem casimir_reduction {J : Type*} (M : J → V →ₗ[ℂ] V)
    (M_mem : ∀ j {n v}, v ∈ C.W n → M j v ∈ C.W n)
    (M_Ω : ∀ j v, M j (C.Ω v) = C.Ω (M j v))
    (M_h : ∀ j v, M j (C.h v) = C.h (M j v))
    {n : ℤ} {u : V} (hu : u ∈ C.W n) (hS : ∀ j, M j u = 0) (hD : C.D u = 0) :
    ∃ u₀ ∈ C.W n, (∀ j, M j u₀ = 0) ∧ (∀ a, C.L a u₀ = 0) ∧ C.D u₀ = 0 ∧
      ∃ w ∈ C.W (n - 1), (∀ j, M j w = 0) ∧ u = u₀ + C.D w := by
  obtain ⟨u₀, hu₀, hΩ₀, x, hx, hux⟩ := C.exists_split hu
  -- choose the preimage in the range part
  obtain ⟨x₀, hx₀, hΩx₀, v, hv, hxv⟩ := C.exists_split hx
  set y := C.Ω v with hydef
  have hy : y ∈ C.W n := C.Ω_mem hv
  have hu1 : u = u₀ + C.Ω y := by rw [hux, hxv, map_add, hΩx₀, zero_add]
  rw [hu1] at hS hD
  -- components of `M_j u`
  have hMsplit (j : J) : M j u₀ = 0 ∧ M j (C.Ω y) = 0 := by
    have hsum : M j u₀ + M j (C.Ω y) = 0 := by rw [← map_add]; exact hS j
    have hk : C.Ω (M j u₀) = 0 := by rw [← M_Ω, hΩ₀, map_zero]
    have hM0 : M j u₀ = 0 := by
      apply C.eq_zero_of_ker_range (M_mem j hu₀) hk (x := -M j y)
        (Submodule.neg_mem _ (M_mem j hy))
      rw [map_neg, ← M_Ω]
      exact (eq_neg_of_add_eq_zero_left hsum).symm
    exact ⟨hM0, by rw [hM0, zero_add] at hsum; exact hsum⟩
  -- components of `D u`
  have hsumD : C.D u₀ + C.D (C.Ω y) = 0 := by rw [← map_add]; exact hD
  have hDu₀ : C.D u₀ = 0 := by
    apply C.eq_zero_of_ker_range (C.D_mem hu₀) (by rw [← D_Ω, hΩ₀, map_zero])
      (x := -C.D y) (Submodule.neg_mem _ (C.D_mem hy))
    rw [map_neg, ← D_Ω]
    exact (eq_neg_of_add_eq_zero_left hsumD).symm
  have hDu₁ : C.D (C.Ω y) = 0 := by rwa [hDu₀, zero_add] at hsumD
  -- `y` is in `S` and is a `D`-cocycle
  have hMy (j : J) : M j y = 0 := by
    apply C.eq_zero_of_ker_range (M_mem j hy) (by rw [← M_Ω]; exact (hMsplit j).2)
      (x := M j v) (M_mem j hv)
    rw [M_Ω]
  have hDy : C.D y = 0 := by
    apply C.eq_zero_of_ker_range (C.D_mem hy) (by rw [← D_Ω]; exact hDu₁)
      (x := C.D v) (C.D_mem hv)
    rw [D_Ω]
  refine ⟨u₀, hu₀, fun j => (hMsplit j).1, fun a => C.L_eq_zero_of_Ω hu₀ hΩ₀ a, hDu₀,
    C.h y, C.h_mem hy, fun j => by rw [M_h, hMy j, map_zero], ?_⟩
  rw [hu1, C.Ω_eq y, hDy, map_zero, add_zero]

end CasimirHomotopy

end KhanSL2.Deformation
