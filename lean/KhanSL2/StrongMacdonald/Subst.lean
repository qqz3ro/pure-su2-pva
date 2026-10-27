module

public import KhanSL2.StrongMacdonald.Grading
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

/-!
# Algebra maps out of `W` and evaluation at even points

* `liftW`: the universal property of `W`. An algebra map out of `W` is given by central images
  of the even generators and anticommuting square-zero images of the odd generators;
  `algHom_ext_W` says it is determined by these images.
* `Deg1`, `substituteLin`: exterior elements of degree one anticommute and square to zero, so
  they may be substituted for the odd generators of `Ext`.
* `evalWith pt M`, `evalAt pt`: evaluation of the even variables at a point `pt : SMode → ℂ`,
  with the odd variables sent to degree-one elements `M` (resp. to themselves).
* `coefPoly x t`: the coefficient of the odd monomial `t` in `x`, as a polynomial in the even
  variables, and the polynomial identity principle `eq_zero_of_evalAt`: an element vanishing at
  all points off a hypersurface `L = 0` is zero.
* `evalAt_congr_of_low`: evaluation only depends on the modes in use.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

/-! ## The universal property of `W` -/

section Lift

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Monomials in central elements `fσ g`, as a monoid map into the center. -/
def sigPowHom (fσ : SMode → A) (hσ : ∀ g (y : A), Commute (fσ g) y) :
    Multiplicative Exp →* Submonoid.center A where
  toFun e := (Multiplicative.toAdd e).prod fun g k =>
    (⟨fσ g, Submonoid.mem_center_iff.mpr fun y => (hσ g y).symm.eq⟩ : Submonoid.center A) ^ k
  map_one' := Finsupp.prod_zero_index
  map_mul' _ _ := Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

/-- The algebra map out of `W` with prescribed central even images and anticommuting
square-zero odd images. -/
def liftW (fσ : SMode → A) (fψ : PMode → A) (hσ : ∀ g (y : A), Commute (fσ g) y)
    (hsq : ∀ m, fψ m * fψ m = 0) (hanti : ∀ m n, fψ m * fψ n = -(fψ n * fψ m)) :
    W →ₐ[ℂ] A :=
  AddMonoidAlgebra.liftNCAlgHom (FiniteExterior.substitute fψ hsq hanti)
    ((Submonoid.center A).subtype.comp (sigPowHom fσ hσ))
    fun _ y => Submonoid.mem_center_iff.mp (sigPowHom fσ hσ y).2 _

variable (fσ : SMode → A) (fψ : PMode → A) (hσ : ∀ g (y : A), Commute (fσ g) y)
  (hsq : ∀ m, fψ m * fψ m = 0) (hanti : ∀ m n, fψ m * fψ n = -(fψ n * fψ m))

theorem liftW_single (e : Exp) (u : Ext) :
    liftW fσ fψ hσ hsq hanti (single e u) =
      FiniteExterior.substitute fψ hsq hanti u *
        (sigPowHom fσ hσ (Multiplicative.ofAdd e) : A) :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

@[simp] theorem liftW_ofExt (u : Ext) :
    liftW fσ fψ hσ hsq hanti (ofExt u) = FiniteExterior.substitute fψ hsq hanti u := by
  rw [ofExt_apply, liftW_single, ofAdd_zero, map_one, OneMemClass.coe_one, mul_one]

@[simp] theorem liftW_sig (g : SMode) : liftW fσ fψ hσ hsq hanti (sig g) = fσ g := by
  rw [sig, liftW_single, map_one, one_mul]
  change (((Finsupp.single g 1).prod fun g k =>
    (⟨fσ g, _⟩ : Submonoid.center A) ^ k : Submonoid.center A) : A) = fσ g
  rw [Finsupp.prod_single_index, pow_one]
  exact pow_zero _

@[simp] theorem liftW_psi (m : PMode) : liftW fσ fψ hσ hsq hanti (psi m) = fψ m := by
  rw [psi_eq, liftW_ofExt, FiniteExterior.substitute_generator]

end Lift

/-- Algebra maps out of `W` are determined by the images of the generators. -/
theorem algHom_ext_W {A : Type*} [Ring A] [Algebra ℂ A] {φ χ : W →ₐ[ℂ] A}
    (hσ : ∀ g, φ (sig g) = χ (sig g)) (hψ : ∀ m, φ (psi m) = χ (psi m)) : φ = χ := by
  refine AlgHom.ext fun x => induction_gen (P := fun x => φ x = χ x) ?_ ?_ ?_ ?_ ?_ ?_ x
  · rw [map_zero, map_zero]
  · rw [map_one, map_one]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro r x hx
    rw [map_smul, map_smul, hx]
  · intro g x hx
    rw [map_mul, map_mul, hx, hσ]
  · intro m x hx
    rw [map_mul, map_mul, hx, hψ]

/-- Postcomposing a lift with an algebra map is again a lift. -/
theorem comp_liftW {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (φ : A →ₐ[ℂ] B) (fσ : SMode → A) (fψ : PMode → A) (hσ : ∀ g (y : A), Commute (fσ g) y)
    (hsq : ∀ m, fψ m * fψ m = 0) (hanti : ∀ m n, fψ m * fψ n = -(fψ n * fψ m))
    (hσ' : ∀ g (y : B), Commute (φ (fσ g)) y) :
    φ.comp (liftW fσ fψ hσ hsq hanti) =
      liftW (fun g => φ (fσ g)) (fun m => φ (fψ m)) hσ'
        (fun m => by rw [← map_mul, hsq, map_zero])
        (fun m n => by rw [← map_mul, ← map_mul, hanti, map_neg]) :=
  algHom_ext_W (fun g => by simp) (fun m => by simp)

/-! ## Homogeneous elements of `W` -/

theorem IsPar.commute_of_even {y : W} (hy : IsPar 0 y) (a : W) : Commute y a :=
  hy.mul_comm' a

theorem IsPar.anticomm {y z : W} (hy : IsPar 1 y) (hz : IsPar 1 z) : y * z = -(z * y) := by
  rw [hy.mul_comm' z, Function.iterate_one, hz, pow_one, neg_one_smul, neg_mul]

theorem IsPar.mul_self_eq_zero {y : W} (hy : IsPar 1 y) : y * y = 0 := by
  have h := hy.anticomm hy
  have h2 : (2 : ℂ) • (y * y) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Substitution into `W`: even images of the even generators, odd images of the odd ones. -/
def substW (fσ : SMode → W) (fψ : PMode → W) (hσ : ∀ g, IsPar 0 (fσ g))
    (hψ : ∀ m, IsPar 1 (fψ m)) : W →ₐ[ℂ] W :=
  liftW fσ fψ (fun g => (hσ g).commute_of_even) (fun m => (hψ m).mul_self_eq_zero)
    (fun m n => (hψ m).anticomm (hψ n))

@[simp] theorem substW_sig (fσ : SMode → W) (fψ : PMode → W) (hσ : ∀ g, IsPar 0 (fσ g))
    (hψ : ∀ m, IsPar 1 (fψ m)) (g : SMode) : substW fσ fψ hσ hψ (sig g) = fσ g :=
  liftW_sig _ _ _ _ _ _

@[simp] theorem substW_psi (fσ : SMode → W) (fψ : PMode → W) (hσ : ∀ g, IsPar 0 (fσ g))
    (hψ : ∀ m, IsPar 1 (fψ m)) (m : PMode) : substW fσ fψ hσ hψ (psi m) = fψ m :=
  liftW_psi _ _ _ _ _ _

/-! ## Degree-one exterior elements -/

/-- Linear combinations of the odd generators of `Ext`. -/
def Deg1 : Submodule ℂ Ext := Submodule.span ℂ (Set.range FiniteExterior.generator)

theorem generator_mem_deg1 (m : PMode) : FiniteExterior.generator m ∈ Deg1 :=
  Submodule.subset_span ⟨m, rfl⟩

theorem parity_of_mem_deg1 {u : Ext} (hu : u ∈ Deg1) : FiniteExterior.parityLinear u = -u := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact FiniteExterior.parity_generator m
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, neg_add]
  | smul r x _ hx => rw [map_smul, hx, smul_neg]

theorem deg1_mul_self {u : Ext} (hu : u ∈ Deg1) : u * u = 0 :=
  FiniteExterior.odd_sq_zero u (parity_of_mem_deg1 hu)

theorem deg1_anticomm {u v : Ext} (hu : u ∈ Deg1) (hv : v ∈ Deg1) : u * v = -(v * u) :=
  FiniteExterior.odd_mul_odd u v (parity_of_mem_deg1 hu) (parity_of_mem_deg1 hv)

/-- Substitute degree-one elements for the odd generators of `Ext`. -/
def substituteLin (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1) : Ext →ₐ[ℂ] Ext :=
  FiniteExterior.substituteOdd M fun m => parity_of_mem_deg1 (hM m)

@[simp] theorem substituteLin_generator (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1) (m : PMode) :
    substituteLin M hM (FiniteExterior.generator m) = M m :=
  FiniteExterior.substituteOdd_generator _ _ m

theorem substituteLin_mem_deg1 (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1) {u : Ext}
    (hu : u ∈ Deg1) : substituteLin M hM u ∈ Deg1 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    rw [substituteLin_generator]
    exact hM m
  | zero => rw [map_zero]; exact Deg1.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact Deg1.add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Deg1.smul_mem r hx

theorem substituteLin_generator_eq_id :
    substituteLin FiniteExterior.generator generator_mem_deg1 = AlgHom.id ℂ Ext :=
  FiniteExterior.algHom_ext _ _ fun m => by simp

/-! ## Evaluation at even points -/

theorem sigPowHom_algebraMap {A : Type*} [Ring A] [Algebra ℂ A] (pt : SMode → ℂ)
    (h : ∀ g (y : A), Commute (algebraMap ℂ A (pt g)) y) (e : Exp) :
    (sigPowHom (fun g => algebraMap ℂ A (pt g)) h (Multiplicative.ofAdd e) : A) =
      algebraMap ℂ A (e.prod fun g k => pt g ^ k) := by
  induction e using Finsupp.induction with
  | zero => rw [ofAdd_zero, map_one, Finsupp.prod_zero_index, map_one, OneMemClass.coe_one]
  | single_add g n e _ hn ih =>
    rw [ofAdd_add, map_mul, Submonoid.coe_mul, ih,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
      Finsupp.prod_single_index (h := fun g k => pt g ^ k) (pow_zero (pt g)), map_mul]
    congr 1
    change (((Finsupp.single g n).prod fun g k =>
      (⟨algebraMap ℂ A (pt g), _⟩ : Submonoid.center A) ^ k : Submonoid.center A) : A) = _
    rw [Finsupp.prod_single_index, SubmonoidClass.coe_pow, map_pow]
    exact pow_zero _

/-- Evaluate the even variables at `pt` and substitute degree-one elements `M` for the odd
variables. -/
def evalWith (pt : SMode → ℂ) (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1) : W →ₐ[ℂ] Ext :=
  liftW (fun g => algebraMap ℂ Ext (pt g)) M
    (fun g y => Algebra.commute_algebraMap_left (pt g) y)
    (fun m => deg1_mul_self (hM m)) (fun m n => deg1_anticomm (hM m) (hM n))

section EvalWith

variable (pt : SMode → ℂ) (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1)

@[simp] theorem evalWith_sig (g : SMode) : evalWith pt M hM (sig g) = algebraMap ℂ Ext (pt g) :=
  liftW_sig _ _ _ _ _ _

@[simp] theorem evalWith_psi (m : PMode) : evalWith pt M hM (psi m) = M m :=
  liftW_psi _ _ _ _ _ _

theorem evalWith_single (e : Exp) (u : Ext) :
    evalWith pt M hM (single e u) = (e.prod fun g k => pt g ^ k) • substituteLin M hM u := by
  rw [evalWith, liftW_single, sigPowHom_algebraMap, ← Algebra.commutes, ← Algebra.smul_def]
  rfl

end EvalWith

/-- Evaluate the even variables at the point `pt`. -/
def evalAt (pt : SMode → ℂ) : W →ₐ[ℂ] Ext :=
  evalWith pt FiniteExterior.generator generator_mem_deg1

section EvalAt

variable (pt : SMode → ℂ)

@[simp] theorem evalAt_sig (g : SMode) : evalAt pt (sig g) = algebraMap ℂ Ext (pt g) :=
  evalWith_sig _ _ _ _

@[simp] theorem evalAt_psi (m : PMode) : evalAt pt (psi m) = FiniteExterior.generator m :=
  evalWith_psi _ _ _ _

theorem evalAt_single (e : Exp) (u : Ext) :
    evalAt pt (single e u) = (e.prod fun g k => pt g ^ k) • u := by
  rw [evalAt, evalWith_single, substituteLin_generator_eq_id, AlgHom.id_apply]

theorem evalAt_mono (e : Exp) (t : Finset PMode) :
    evalAt pt (mono e t) = (e.prod fun g k => pt g ^ k) • FiniteExterior.monomial t :=
  evalAt_single pt e _

@[simp] theorem evalAt_ofExt (u : Ext) : evalAt pt (ofExt u) = u := by
  rw [ofExt_apply, evalAt_single, Finsupp.prod_zero_index, one_smul]

theorem evalAt_surjective : Function.Surjective (evalAt pt) :=
  fun u => ⟨ofExt u, evalAt_ofExt pt u⟩

end EvalAt

/-! ## Precomposition with substitutions -/

/-- An odd substitution after evaluation is evaluation with degree-one odd images. -/
theorem substituteLin_comp_evalWith (pt : SMode → ℂ) (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1)
    (M' : PMode → Ext) (hM' : ∀ m, M' m ∈ Deg1) :
    (substituteLin M' hM').comp (evalWith pt M hM) =
      evalWith pt (fun m => substituteLin M' hM' (M m))
        (fun m => substituteLin_mem_deg1 M' hM' (hM m)) :=
  algHom_ext_W (fun g => by simp) (fun m => by simp)

theorem substituteLin_comp_evalAt (pt : SMode → ℂ) (M : PMode → Ext) (hM : ∀ m, M m ∈ Deg1) :
    (substituteLin M hM).comp (evalAt pt) = evalWith pt M hM :=
  algHom_ext_W (fun g => by simp) (fun m => by simp)

/-- Images of central elements under `evalAt` are central (`evalAt` is surjective). -/
theorem commute_evalAt {x : W} (hx : ∀ y : W, Commute x y) (pt : SMode → ℂ) (u : Ext) :
    Commute (evalAt pt x) u := by
  obtain ⟨y, rfl⟩ := evalAt_surjective pt u
  exact (hx y).map (evalAt pt)

/-- Evaluation after a substitution into `W` is again a lift. -/
theorem evalAt_comp_liftW (pt : SMode → ℂ) (fσ : SMode → W) (fψ : PMode → W)
    (hσ : ∀ g (y : W), Commute (fσ g) y)
    (hsq : ∀ m, fψ m * fψ m = 0) (hanti : ∀ m n, fψ m * fψ n = -(fψ n * fψ m)) :
    (evalAt pt).comp (liftW fσ fψ hσ hsq hanti) =
      liftW (fun g => evalAt pt (fσ g)) (fun m => evalAt pt (fψ m))
        (fun g => commute_evalAt (hσ g) pt)
        (fun m => by rw [← map_mul, hsq, map_zero])
        (fun m n => by rw [← map_mul, ← map_mul, hanti, map_neg]) :=
  comp_liftW _ _ _ _ _ _ _

/-! ## Coefficient polynomials -/

/-- The coefficient of the odd monomial `t`, as a polynomial in the even variables. -/
def coefPoly (x : W) (t : Finset PMode) : MvPolynomial SMode ℂ :=
  ∑ e ∈ x.coeff.support, MvPolynomial.monomial e (coefW x e t)

@[simp] theorem coeff_coefPoly (x : W) (t : Finset PMode) (e : Exp) :
    (coefPoly x t).coeff e = coefW x e t := by
  classical
  rw [coefPoly, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · simp [coefW, not_not.mp h]

@[simp] theorem coefPoly_zero (t : Finset PMode) : coefPoly 0 t = 0 := by
  ext e; simp

@[simp] theorem coefPoly_add (x y : W) (t : Finset PMode) :
    coefPoly (x + y) t = coefPoly x t + coefPoly y t := by
  ext e; simp

@[simp] theorem coefPoly_smul (c : ℂ) (x : W) (t : Finset PMode) :
    coefPoly (c • x) t = c • coefPoly x t := by
  ext e; simp

theorem coefPoly_mono (e : Exp) (s t : Finset PMode) :
    coefPoly (mono e s) t = if s = t then MvPolynomial.monomial e 1 else 0 := by
  classical
  ext e'
  rw [coeff_coefPoly, coefW_mono]
  split_ifs with h1 h2 h2
  · rw [MvPolynomial.coeff_monomial, if_pos h1.1]
  · exact absurd h1.2 h2
  · rw [MvPolynomial.coeff_monomial, if_neg fun he => h1 ⟨he, h2⟩]
  · simp

theorem evalAt_apply_coeff (pt : SMode → ℂ) (x : W) (t : Finset PMode) :
    (evalAt pt x) t = MvPolynomial.eval pt (coefPoly x t) := by
  refine mono_induction (P := fun x => (evalAt pt x) t = MvPolynomial.eval pt (coefPoly x t))
    ?_ ?_ ?_ ?_ x
  · simp
  · intro x y hx hy
    rw [map_add, Finsupp.add_apply, hx, hy, coefPoly_add, map_add]
  · intro c x hx
    rw [map_smul, Finsupp.smul_apply, hx, coefPoly_smul, MvPolynomial.smul_eval, smul_eq_mul,
      mul_comm]
  · intro e s
    rw [evalAt_mono, coefPoly_mono, Finsupp.smul_apply, FiniteExterior.monomial,
      Finsupp.single_apply]
    split_ifs with h
    · rw [MvPolynomial.eval_monomial, smul_eq_mul, mul_one, one_mul]
    · rw [map_zero, smul_zero]

theorem eq_zero_of_coefPoly {x : W} (h : ∀ t, coefPoly x t = 0) : x = 0 := by
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  ext e t
  have := congrArg (fun p : MvPolynomial SMode ℂ => p.coeff e) (h t)
  simpa [coefW] using this

/-- Polynomial identity principle: an element of `W` whose evaluations vanish off the
hypersurface `L = 0` is zero. -/
theorem eq_zero_of_evalAt {x : W} {L : MvPolynomial SMode ℂ} (hL : L ≠ 0)
    (h : ∀ pt, MvPolynomial.eval pt L ≠ 0 → evalAt pt x = 0) : x = 0 := by
  refine eq_zero_of_coefPoly fun t => ?_
  have hprod : L * coefPoly x t = 0 := by
    refine MvPolynomial.funext fun pt => ?_
    rw [map_mul, map_zero]
    by_cases hpt : MvPolynomial.eval pt L = 0
    · rw [hpt, zero_mul]
    · rw [← evalAt_apply_coeff, h pt hpt, Finsupp.zero_apply, mul_zero]
  exact (mul_eq_zero.mp hprod).resolve_left hL

/-- An element of `W` whose evaluations all vanish is zero. -/
theorem eq_zero_of_evalAt_all {x : W} (h : ∀ pt, evalAt pt x = 0) : x = 0 :=
  eq_zero_of_evalAt one_ne_zero fun pt _ => h pt

/-! ## Only the modes in use matter -/

theorem evalWith_congr_of_low {N : ℕ} {x : W} (hx : Low N x) {pt pt' : SMode → ℂ}
    {M M' : PMode → Ext} (hM : ∀ m, M m ∈ Deg1) (hM' : ∀ m, M' m ∈ Deg1)
    (hpt : ∀ g : SMode, g.index < N → pt g = pt' g)
    (hMM : ∀ m : PMode, m.index < N → M m = M' m) :
    evalWith pt M hM x = evalWith pt' M' hM' x := by
  induction hx with
  | zero => rw [map_zero, map_zero]
  | one => rw [map_one, map_one]
  | add _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul r _ hx => rw [map_smul, map_smul, hx]
  | sig hg _ hx => rw [map_mul, map_mul, hx, evalWith_sig, evalWith_sig, hpt _ hg]
  | psi hm _ hx => rw [map_mul, map_mul, hx, evalWith_psi, evalWith_psi, hMM _ hm]

theorem evalAt_congr_of_low {N : ℕ} {x : W} (hx : Low N x) {pt pt' : SMode → ℂ}
    (h : ∀ g : SMode, g.index < N → pt g = pt' g) : evalAt pt x = evalAt pt' x :=
  evalWith_congr_of_low hx _ _ h fun _ _ => rfl

end KhanSL2.StrongMacdonald
