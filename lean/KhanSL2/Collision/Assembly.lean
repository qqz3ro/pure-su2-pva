module

public import KhanSL2.Collision.Statements
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Support

@[expose] public section

/-!
# Assembly of the collision-support step from chart factorizations

* `chartComparison_of_factor`: `KFactor B` and `JFactor B` give `ChartComparison B`
  (base change of the smaller comparisons `ψ_{B_i}`, which are isomorphisms by induction).
* `collisionSupportStep_of_chartComparison`: the chart comparisons give
  `Conditional.CollisionSupportStep`.

Proof of the second statement. Let `𝔭 ∈ Supp ker ψ_{B,p}` with `P_B ⊄ 𝔭`. As `R_B` is Jacobson,
there is a maximal `𝔪 ⊇ 𝔭` with `P_B ⊄ 𝔪`, still in the support. By the Nullstellensatz `𝔪` is a
point `x ∈ ℂ^B`; the specialization of `F_B` at `x` is not a pure power `(u - a)^B` (otherwise all
collision generators vanish at `x`), so it splits into coprime monic factors of positive degree.
Mathlib's universal coprime factorization ring gives an étale chart `A` with a prime `Q` over `𝔪`.
On `A`, `A ⊗ ψ` is a surjection between modules isomorphic to `A ⊗ K ≅ A ⊗ J` with `A ⊗ J`
finite, hence injective (Orzech); by flatness `A ⊗ ker ψ = 0`, and since `Q` lies over `𝔪` this
forces `𝔪 ∉ Supp ker ψ`.
-/

noncomputable section

open Polynomial TensorProduct
open scoped DirectSum

namespace KhanSL2.Collision

open Conditional
open scoped KhanSL2.Conditional

/-- Under the induction hypothesis, the smaller comparisons are linear equivalences. -/
def psiEquiv {B : ℕ} (hE : EarlierComparisons B) (b : ℕ) (hb : b < B) (q : ℕ) :
    K b q ≃ₗ[Depth.RB b] J b q :=
  LinearEquiv.ofBijective (Conditional.psi b q) ⟨hE b hb q, Conditional.psi_surjective b q⟩

/-- **Chart comparison** from the factorizations of `K` and `J`. -/
theorem chartComparison_of_factor (B : ℕ) (hK : KFactor B) (hJ : JFactor B) :
    ChartComparison B := by
  intro hE B₁ B₂ h₁ h₂ hsum A _ _ _ c p
  let eK := (hK B₁ B₂ h₁ h₂ hsum A c p).some
  let eJ := (hJ B₁ B₂ h₁ h₂ hsum A c p).some
  let _ := c.algebra₁
  let _ := c.algebra₂
  have mid : FactorSide c (K B₁) (K B₂) p ≃ₗ[A] FactorSide c (J B₁) (J B₂) p :=
    DirectSum.congrLinearEquiv fun q =>
      TensorProduct.congr
        ((psiEquiv hE B₁ (by omega) q).baseChange (Depth.RB B₁) A _ _)
        ((psiEquiv hE B₂ (by omega) (p - q)).baseChange (Depth.RB B₂) A _ _)
  exact ⟨eK.trans (mid.trans eJ.symm)⟩

section ModuleTheory

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Let `f : M → N` be surjective with `N` finite, and `A` flat over `R`. If `A ⊗ M ≅ A ⊗ N`
(abstractly, as `A`-modules), then `A ⊗ ker f = 0`: the surjection `A ⊗ f` is injective by the
Orzech property of commutative rings, and `A ⊗ ker f = ker (A ⊗ f)` by flatness. -/
theorem subsingleton_baseChange_ker [Module.Flat R A] [Module.Finite R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (e : A ⊗[R] M ≃ₗ[A] A ⊗[R] N) :
    Subsingleton (A ⊗[R] LinearMap.ker f) := by
  have hsurj : Function.Surjective (f.baseChange A) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective A hf
  have hinj : Function.Injective (f.baseChange A) := by
    have h2 : Function.Surjective (f.baseChange A ∘ₗ e.symm.toLinearMap) :=
      hsurj.comp e.symm.surjective
    have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
    have : (f.baseChange A) = (f.baseChange A ∘ₗ e.symm.toLinearMap) ∘ₗ e.toLinearMap := by
      ext x; simp
    rw [this]
    exact h3.comp e.injective
  have hk : Function.Injective ((LinearMap.ker f).subtype.lTensor A) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (LinearMap.ker f).injective_subtype
  refine ⟨fun x y => hk (hinj ?_)⟩
  rw [LinearMap.baseChange_eq_lTensor]
  simp only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  have : f ∘ₗ (LinearMap.ker f).subtype = 0 := by ext x; simp
  rw [this]
  simp

/-- If `A` is flat over `R`, `A ⊗ M = 0` and some prime `Q` of `A` lies over `P`, then
`P ∉ Supp M`: for `m` with `ann m ⊆ P`, flatness gives `A / (ann m) A = A ⊗ R/(ann m) ↪ A ⊗ M = 0`,
but `(ann m) A ⊆ Q`. -/
theorem notMem_support_of_subsingleton_baseChange [Module.Flat R A]
    (h : Subsingleton (A ⊗[R] M)) (Q : Ideal A) [Q.IsPrime] (P : PrimeSpectrum R)
    (hQ : Q.comap (algebraMap R A) = P.asIdeal) : P ∉ Module.support R M := by
  intro hP
  obtain ⟨m, hm⟩ := Module.mem_support_iff_exists_annihilator.mp hP
  let φ := LinearMap.toSpanSingleton R M m
  let I : Ideal R := LinearMap.ker φ
  have hI : I ≤ P.asIdeal := by
    intro r hr
    apply hm
    rw [Submodule.mem_annihilator_span_singleton]
    exact hr
  let ψ : (R ⧸ I) →ₗ[R] M := Submodule.liftQ I φ le_rfl
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hsub : Subsingleton (A ⊗[R] (R ⧸ I)) := by
    refine ⟨fun x y => Module.Flat.lTensor_preserves_injective_linearMap ψ hψ ?_⟩
    exact Subsingleton.elim _ _
  have hq : Subsingleton (A ⧸ I.map (algebraMap R A)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).toEquiv.subsingleton
  rw [Ideal.Quotient.subsingleton_iff] at hq
  have : I.map (algebraMap R A) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, hQ]
    exact hI
  exact (‹Q.IsPrime›.ne_top) (top_le_iff.mp (hq ▸ this))

end ModuleTheory

/-! ### The universal polynomial away from the collision locus -/

theorem univPoly_monic (B : ℕ) : (univPoly B).Monic := Depth.monicOf_monic _ _

theorem natDegree_univPoly (B : ℕ) : (univPoly B).natDegree = B := Depth.natDegree_monicOf _ _

/-- The coefficients of the specialization of `F_B` at a point `x ∈ ℂ^B`. -/
theorem coeff_univPoly_map_eval (B : ℕ) (x : Fin B → ℂ) (k : ℕ) (hk : k < B) :
    ((univPoly B).map (MvPolynomial.eval x)).coeff k =
      (-1) ^ (B - k) * x ⟨B - 1 - k, by omega⟩ := by
  rw [Polynomial.coeff_map]
  have := Depth.coeff_monicOf B (fun k : Fin B => ((-1 : ℂ) ^ (B - (k : ℕ))) •
    MvPolynomial.X (R := ℂ) (⟨B - 1 - (k : ℕ), by omega⟩ : Fin B)) ⟨k, hk⟩
  rw [univPoly, this, MvPolynomial.smul_eval, MvPolynomial.eval_X]

/-- If the universal polynomial specializes to a pure power `(u - a)^B` at `x`, then all the
collision generators vanish at `x`. -/
theorem eval_collisionGen_of_eq_pow (B : ℕ) (x : Fin B → ℂ) (a : ℂ)
    (h : (univPoly B).map (MvPolynomial.eval x) = (X - C a) ^ B) (j : Fin B) :
    MvPolynomial.eval x (Depth.collisionGen B j) = 0 := by
  have hx : ∀ j : Fin B, x j = (B.choose ((j : ℕ) + 1) : ℂ) * a ^ ((j : ℕ) + 1) := by
    intro j
    have hj := j.isLt
    have := congrArg (fun q => q.coeff (B - 1 - j)) h
    rw [coeff_univPoly_map_eval B x _ (by omega), sub_eq_add_neg, ← C_neg,
      coeff_X_add_C_pow] at this
    have e1 : B - (B - 1 - (j : ℕ)) = (j : ℕ) + 1 := by omega
    have e2 : B - 1 - (B - 1 - (j : ℕ)) = (j : ℕ) := by omega
    have e3 : B.choose (B - 1 - (j : ℕ)) = B.choose ((j : ℕ) + 1) := by
      rw [show B - 1 - (j : ℕ) = B - ((j : ℕ) + 1) by omega, Nat.choose_symm (by omega)]
    simp only [e1, e2, e3, Fin.eta, neg_pow (a := a)] at this
    have hu : ((-1 : ℂ) ^ ((j : ℕ) + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    apply mul_left_cancel₀ hu
    rw [this]
    ring
  have hB : (B : ℂ) ≠ 0 := by
    have := j.pos
    exact_mod_cast this.ne'
  have h0 := hx ⟨0, j.pos⟩
  simp only [zero_add, Nat.choose_one_right, pow_one] at h0
  rw [Depth.collisionGen, map_sub, map_mul, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C,
    MvPolynomial.eval_X, hx j, h0, Depth.collisionCoeff]
  field_simp
  ring

/-- If the universal polynomial specializes to `(u - a)^B` at `x`, then `P_B ⊆ 𝔪_x`. -/
theorem collisionIdeal_le_of_eq_pow (B : ℕ) (x : Fin B → ℂ) (a : ℂ)
    (h : (univPoly B).map (MvPolynomial.eval x) = (X - C a) ^ B) :
    Depth.collisionIdeal B ≤ MvPolynomial.vanishingIdeal ℂ {x} := by
  rw [Depth.collisionIdeal, Ideal.ofList, Ideal.span_le]
  intro g hg
  obtain ⟨j, -, rfl⟩ := Depth.mem_collisionList hg
  rw [SetLike.mem_coe, MvPolynomial.mem_vanishingIdeal_singleton_iff]
  exact eval_collisionGen_of_eq_pow B x a h j

/-- Splitting off the full multiplicity of one root. -/
theorem exists_coprime_factor_of_root {F : ℂ[X]} (hF : F.Monic) (a : ℂ) (ha : F.IsRoot a)
    (hnot : F ≠ (X - C a) ^ F.natDegree) :
    ∃ f g : ℂ[X], f.Monic ∧ g.Monic ∧ F = f * g ∧ IsCoprime f g ∧
      0 < f.natDegree ∧ 0 < g.natDegree := by
  generalize hn' : rootMultiplicity a F = n
  have hfac := pow_mul_divByMonic_rootMultiplicity_eq F a
  rw [hn'] at hfac
  have hfm : ((X - C a) ^ n).Monic := (monic_X_sub_C a).pow n
  have hgm : (F /ₘ (X - C a) ^ n).Monic := hfm.of_mul_monic_left (by rw [hfac]; exact hF)
  have hn : 0 < n := hn' ▸ (rootMultiplicity_pos hF.ne_zero).mpr ha
  refine ⟨(X - C a) ^ n, F /ₘ (X - C a) ^ n, hfm, hgm, hfac.symm, ?_, ?_, ?_⟩
  · apply IsCoprime.pow_left
    rw [(irreducible_X_sub_C a).coprime_iff_not_dvd, dvd_iff_isRoot, ← hn']
    exact eval_divByMonic_pow_rootMultiplicity_ne_zero a hF.ne_zero
  · rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact hn
  · by_contra h0
    have h1 : F /ₘ (X - C a) ^ n = 1 := (Polynomial.Monic.natDegree_eq_zero hgm).mp (by omega)
    rw [h1, mul_one] at hfac
    apply hnot
    rw [← hfac, natDegree_pow, natDegree_X_sub_C, mul_one]

/-- A monic complex polynomial of positive degree which is not a pure power of a linear factor
splits into two coprime monic factors of positive degree. -/
theorem exists_coprime_factor {F : ℂ[X]} (hF : F.Monic) (hdeg : 0 < F.natDegree)
    (hnot : ∀ a, F ≠ (X - C a) ^ F.natDegree) :
    ∃ f g : ℂ[X], f.Monic ∧ g.Monic ∧ F = f * g ∧ IsCoprime f g ∧
      0 < f.natDegree ∧ 0 < g.natDegree := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root F (by
    rw [degree_eq_natDegree hF.ne_zero]; exact_mod_cast hdeg.ne')
  exact exists_coprime_factor_of_root hF a ha (hnot a)

/-- **Charts away from the collision locus.** At a maximal ideal `𝔪` of `R_B` not containing
the collision ideal, there is a chart with a prime lying over `𝔪`. -/
theorem exists_chart (B : ℕ) (hB : 0 < B) (𝔪 : Ideal (Depth.RB B)) [h𝔪 : 𝔪.IsMaximal]
    (hcol : ¬ Depth.collisionIdeal B ≤ 𝔪) :
    ∃ (B₁ B₂ : ℕ) (_ : 0 < B₁) (_ : 0 < B₂) (_ : B₁ + B₂ = B) (A : Type) (_ : CommRing A)
      (_ : Algebra (Depth.RB B) A) (_ : Algebra.Etale (Depth.RB B) A) (_ : ChartData B B₁ B₂ A)
      (Q : Ideal A) (_ : Q.IsPrime), Q.comap (algebraMap (Depth.RB B) A) = 𝔪 := by
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ h𝔪
  let F : ℂ[X] := (univPoly B).map (MvPolynomial.eval x)
  have hFm : F.Monic := (univPoly_monic B).map _
  have hFd : F.natDegree = B := by
    rw [(univPoly_monic B).natDegree_map, natDegree_univPoly]
  have hnot : ∀ a, F ≠ (X - C a) ^ F.natDegree := by
    intro a ha
    rw [hFd] at ha
    exact hcol (hx ▸ collisionIdeal_le_of_eq_pow B x a ha)
  obtain ⟨f, g, hf, hg, hFfg, hcop, hf0, hg0⟩ := exists_coprime_factor hFm (hFd ▸ hB) hnot
  let φ : ℂ →+* 𝔪.ResidueField := (algebraMap (Depth.RB B) 𝔪.ResidueField).comp MvPolynomial.C
  have hφ : algebraMap (Depth.RB B) 𝔪.ResidueField = φ.comp (MvPolynomial.eval x) := by
    refine RingHom.ext fun r => ?_
    simp only [φ, RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero, hx,
      MvPolynomial.mem_vanishingIdeal_singleton_iff]
    change MvPolynomial.eval x _ = 0
    simp
  have hmap : (univPoly B).map (algebraMap _ 𝔪.ResidueField) = f.map φ * g.map φ := by
    rw [← Polynomial.map_mul, ← hFfg, Polynomial.map_map, hφ]
  obtain ⟨A, _, _, _, Q, _, hQ, f', g', -, hf', hg', hfac, hcop', hff', hgg'⟩ :=
    Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime 𝔪 (univPoly B)
      (f.map φ) (g.map φ) (univPoly_monic B) (hf.map φ) (hg.map φ) hmap
      (hcop.map (Polynomial.mapRingHom φ))
  have hdf : f'.natDegree = f.natDegree := by
    have := congrArg natDegree hff'
    rw [hf'.natDegree_map, (hf.map φ).natDegree_map, hf.natDegree_map] at this
    exact this.symm
  have hdg : g'.natDegree = g.natDegree := by
    have := congrArg natDegree hgg'
    rw [hg'.natDegree_map, (hg.map φ).natDegree_map, hg.natDegree_map] at this
    exact this.symm
  have hsum : f.natDegree + g.natDegree = B := by rw [← hf.natDegree_mul hg, ← hFfg, hFd]
  have c : ChartData B f.natDegree g.natDegree A := ⟨f', g', hf', hg', hdf, hdg, hfac, hcop'⟩
  exact ⟨f.natDegree, g.natDegree, hf0, hg0, hsum, A, _, _, ‹_›, c, Q, ‹_›,
    (Ideal.over_def Q 𝔪).symm⟩

/-! ### Assembly -/

/-- The polynomial target `J_{B,p}` is a finite `R_B`-module. -/
theorem finite_J (B p : ℕ) : Module.Finite (Depth.RB B) (J B p) := by
  show Module.Finite (Depth.RB B) (Depth.JB B p)
  by_cases h : p ≤ B ∧ 3 ∣ B - p
  · rw [Depth.JB, if_pos h]
    obtain ⟨_, k, hk⟩ := h
    have hs : (B - p) / 3 = k := by omega
    rw [hs]
    obtain rfl : B = p + 3 * k := by omega
    exact Depth.J_finite p k
  · rw [Depth.JB, if_neg h]
    exact Module.Finite.iff_fg.mpr Submodule.fg_bot

/-- **The collision-support step** from the chart comparisons. -/
theorem collisionSupportStep_of_chartComparison (h : ∀ B, ChartComparison B) :
    Conditional.CollisionSupportStep := by
  intro B hB hE p hp2 hpB P hP
  rw [PrimeSpectrum.mem_zeroLocus]
  by_contra hcol
  obtain ⟨𝔪, h𝔪, hP𝔪, hcol𝔪⟩ : ∃ 𝔪 : Ideal (Depth.RB B), 𝔪.IsMaximal ∧ P.asIdeal ≤ 𝔪 ∧
      ¬ Depth.collisionIdeal B ≤ 𝔪 := by
    by_contra hall
    push Not at hall
    apply hcol
    have hjac : P.asIdeal.jacobson = P.asIdeal :=
      IsJacobsonRing.out inferInstance P.isPrime.isRadical
    show Depth.collisionIdeal B ≤ P.asIdeal
    rw [← hjac]
    exact le_sInf fun I ⟨hPI, hI⟩ => hall I hI hPI
  have hM : (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum (Depth.RB B)) ∈
      Module.support (Depth.RB B) (LinearMap.ker (Conditional.psi B p)) :=
    Module.mem_support_mono (q := ⟨𝔪, h𝔪.isPrime⟩) hP𝔪 hP
  obtain ⟨B₁, B₂, h₁, h₂, hsum, A, _, _, _, c, Q, _, hQ⟩ := exists_chart B hB 𝔪 hcol𝔪
  let e := (h B hE B₁ B₂ h₁ h₂ hsum A c p).some
  have : Module.Finite (Depth.RB B) (J B p) := finite_J B p
  exact notMem_support_of_subsingleton_baseChange
    (subsingleton_baseChange_ker (Conditional.psi B p) (Conditional.psi_surjective B p) e)
    Q _ hQ hM

end KhanSL2.Collision
