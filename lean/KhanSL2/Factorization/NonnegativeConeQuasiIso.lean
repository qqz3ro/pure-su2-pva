module

public import KhanSL2.Factorization.NonnegativeCone

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.NonnegativeCone

universe u v
variable {R : Type u} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{v} R) ℕ} (φ : C ⟶ D)

abbrev IsCycle (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (x : C.X n) : Prop :=
  C.d n (n-1) x = 0

theorem isCycle_zero (x : C.X 0) : IsCycle C 0 x := by
  change C.d 0 0 x = 0
  rw [C.shape _ _ (by simp)]
  rfl

theorem target_pair_cycle (n : ℕ) (y : D.X (n+1)) (hy : D.d (n+1) n y = 0) :
    differential φ n (y,0) = 0 := by
  cases n with
  | zero =>
    change D.d 1 0 y + φ.f 0 0 = 0
    rw [map_zero,add_zero]
    exact hy
  | succ n =>
    change (D.d (n+2) (n+1) y + φ.f (n+1) 0,-C.d (n+1) n 0) = (0,0)
    rw [map_zero,map_zero,hy,zero_add,neg_zero]

theorem source_pair_cycle (n : ℕ) (x : C.X n) (hx : IsCycle C n x)
    (z : D.X (n+1)) (hz : φ.f n x = D.d (n+1) n z) :
    differential φ n (-z,x) = 0 := by
  cases n with
  | zero =>
    change D.d 1 0 (-z) + φ.f 0 x = 0
    rw [map_neg,hz,neg_add_cancel]
  | succ n =>
    change C.d (n+1) n x = 0 at hx
    change (D.d (n+2) (n+1) (-z) + φ.f (n+1) x,-C.d (n+1) n x) = (0,0)
    rw [map_neg,hz,neg_add_cancel,hx,neg_zero]

/-- Acyclicity of the genuine cone gives the canonical quasi-isomorphism. -/
theorem quasiIso_of_acyclic (hc : (complex φ).Acyclic) : QuasiIso φ := by
  have hd := (ComplexExactness.acyclic_iff (complex φ)).mp hc
  have h₀ : Function.Surjective (differential φ 0) := by
    have h₀ := hd.1
    change Function.Surjective (differential φ 0) at h₀
    exact h₀
  have h : ∀ n, Function.Exact (differential φ (n+1)) (differential φ n) := by
    intro n
    have hn := hd.2 n
    rw [show n+2 = (n+1)+1 from rfl,complex_d,complex_d] at hn
    exact hn
  have hsurj : ∀ n (y : D.X n), IsCycle D n y →
      ∃ x : C.X n, IsCycle C n x ∧ ∃ z : D.X (n+1), φ.f n x - y = D.d (n+1) n z := by
    intro n y hy
    cases n with
    | zero =>
      obtain ⟨⟨z,x⟩,hz⟩ := h₀ y
      refine ⟨x,isCycle_zero x,-z,?_⟩
      change D.d 1 0 z + φ.f 0 x = y at hz
      rw [map_neg,← hz]
      abel
    | succ n =>
      have hy' : D.d (n+1) n y = 0 := by change D.d (n+1) n y = 0 at hy; exact hy
      obtain ⟨⟨z,x⟩,hz⟩ := (h n (y,0)).mp (target_pair_cycle φ n y hy')
      have hfirst := congrArg Prod.fst hz
      have hsecond := congrArg Prod.snd hz
      change D.d (n+2) (n+1) z + φ.f (n+1) x = y at hfirst
      change -C.d (n+1) n x = 0 at hsecond
      refine ⟨x,?_, -z,?_⟩
      · change C.d (n+1) n x = 0
        exact neg_eq_zero.mp hsecond
      · rw [map_neg,← hfirst]
        abel
  have hinj : ∀ n (x : C.X n), IsCycle C n x →
      (∃ z : D.X (n+1), φ.f n x = D.d (n+1) n z) →
      ∃ w : C.X (n+1), C.d (n+1) n w = x := by
    intro n x hx ⟨z,hz⟩
    obtain ⟨⟨w,b⟩,hb⟩ := (h n (-z,x)).mp (source_pair_cycle φ n x hx z hz)
    have hb' := congrArg Prod.snd hb
    change -C.d (n+1) n b = x at hb'
    exact ⟨-b,by rw [map_neg]; exact hb'⟩
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' φ (n+1) n (n-1) (by simp) (by cases n <;> simp)]
  exact QuasiIsoElements.quasiIso_of_cycles _ (hsurj n) (hinj n)

/-- A quasi-isomorphism has acyclic cone, including the bottom degree. -/
theorem acyclic_of_quasiIso [QuasiIso φ] : (complex φ).Acyclic := by
  have hcycles (n : ℕ) := by
    have hi : QuasiIsoAt φ n := inferInstance
    have hs := (quasiIsoAt_iff' φ (n+1) n (n-1) (by simp) (by cases n <;> simp)).mp hi
    let := hs
    exact QuasiIsoElements.cycles_of_quasiIso
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (ComplexShape.down ℕ)
        (n+1) n (n-1)).map φ)
  have hsurj : ∀ n (y : D.X n), IsCycle D n y →
      ∃ x : C.X n, IsCycle C n x ∧ ∃ z : D.X (n+1), φ.f n x - y = D.d (n+1) n z :=
    fun n => (hcycles n).1
  have hinj : ∀ n (x : C.X n), IsCycle C n x →
      (∃ z : D.X (n+1), φ.f n x = D.d (n+1) n z) →
      ∃ w : C.X (n+1), C.d (n+1) n w = x := fun n => (hcycles n).2
  apply (ComplexExactness.acyclic_iff (complex φ)).mpr
  constructor
  · change Function.Surjective (differential φ 0)
    intro y
    obtain ⟨x,hx,z,hz⟩ := hsurj 0 y (isCycle_zero y)
    refine ⟨(-z,x),?_⟩
    change D.d 1 0 (-z) + φ.f 0 x = y
    rw [map_neg,sub_eq_iff_eq_add.mp hz,neg_add_cancel_left]
  · intro n
    simp only [complex_d,ModuleCat.hom_ofHom]
    change Function.Exact (differential φ (n+1)) (differential φ n)
    apply LinearMap.exact_of_comp_of_mem_range (square φ n)
    intro v hv
    rcases v with ⟨y,x⟩
    have hx : IsCycle C n x := by
      cases n with
      | zero => exact isCycle_zero x
      | succ n =>
        have hx' := congrArg Prod.snd hv
        change -C.d (n+1) n x = 0 at hx'
        exact neg_eq_zero.mp hx'
    have hφ : φ.f n x = D.d (n+1) n (-y) := by
      have he : D.d (n+1) n y + φ.f n x = 0 := by
        cases n with
        | zero => exact hv
        | succ n => exact congrArg Prod.fst hv
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_right he
    obtain ⟨b,hb⟩ := hinj n x hx ⟨-y,hφ⟩
    have hy : IsCycle D (n+1) (y + φ.f (n+1) b) := by
      change D.d (n+1) n (y + φ.f (n+1) b) = 0
      rw [map_add,comm_apply,hb,hφ,map_neg,add_neg_cancel]
    obtain ⟨c,hc,z,hz⟩ := hsurj (n+1) (y + φ.f (n+1) b) hy
    refine ⟨(-z,c-b),?_⟩
    apply Prod.ext
    · change D.d (n+2) (n+1) (-z) + φ.f (n+1) (c-b) = y
      rw [map_neg,map_sub,← hz]
      abel
    · change -C.d (n+1) n (c-b) = x
      change C.d (n+1) n c = 0 at hc
      rw [map_sub,hc,zero_sub,neg_neg,hb]

/-- The cone criterion used for both residue detection and arbitrary base change. -/
theorem quasiIso_iff_acyclic : QuasiIso φ ↔ (complex φ).Acyclic :=
  ⟨fun h => by let := h; exact acyclic_of_quasiIso φ,quasiIso_of_acyclic φ⟩

end KhanSL2.Factorization.NonnegativeCone
