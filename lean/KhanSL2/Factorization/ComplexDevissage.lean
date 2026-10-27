module

public import KhanSL2.Factorization.NonnegativeConeQuasiIso

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.ComplexExactness

universe u v
variable {R : Type u} [CommRing R]
variable {C D E : ChainComplex (ModuleCat.{v} R) ℕ}

theorem map_d_apply (f : C ⟶ D) (a b : ℕ) (x : C.X a) :
    D.d a b (f.f a x) = f.f b (C.d a b x) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.comm a b)) x

theorem acyclic_iff_cycles (C : ChainComplex (ModuleCat.{v} R) ℕ) :
    C.Acyclic ↔ ∀ n (x : C.X n), C.d n (n-1) x = 0 →
      ∃ y : C.X (n+1), C.d (n+1) n y = x := by
  constructor
  · intro h n
    exact (ShortComplex.moduleCat_exact_iff _).mp
      ((C.exactAt_iff' (n+1) n (n-1) (by simp) (by cases n <;> simp)).mp (h n))
  · intro h n
    apply (C.exactAt_iff' (n+1) n (n-1) (by simp) (by cases n <;> simp)).mpr
    exact (ShortComplex.moduleCat_exact_iff _).mpr (h n)

/-- A degreewise short exact sequence of actual nonnegative complexes preserves
acyclicity under extensions. The coefficient splittings need not be chain maps. -/
theorem acyclic_of_shortExact (i : C ⟶ D) (p : D ⟶ E)
    (hinj : ∀ n, Function.Injective (i.f n))
    (hex : ∀ n, Function.Exact (i.f n) (p.f n))
    (hsurj : ∀ n, Function.Surjective (p.f n))
    (hC : C.Acyclic) (hE : E.Acyclic) : D.Acyclic := by
  apply (acyclic_iff_cycles D).mpr
  intro n y hy
  have hpcycle : E.d n (n-1) (p.f n y) = 0 := by
    rw [map_d_apply,hy,map_zero]
  obtain ⟨z₃,hz₃⟩ := (acyclic_iff_cycles E).mp hE n (p.f n y) hpcycle
  obtain ⟨z₂,hz₂⟩ := hsurj (n+1) z₃
  have hpcorr : p.f n (y - D.d (n+1) n z₂) = 0 := by
    rw [map_sub,← map_d_apply,hz₂,hz₃,sub_self]
  obtain ⟨x,hx⟩ := (hex n (y - D.d (n+1) n z₂)).mp hpcorr
  have hxcycle : C.d n (n-1) x = 0 := by
    apply hinj (n-1)
    rw [map_zero,← map_d_apply,hx,map_sub,hy]
    have hd := congrArg (fun f => f z₂) (D.d_comp_d (n+1) n (n-1))
    change D.d n (n-1) (D.d (n+1) n z₂) = 0 at hd
    rw [hd,sub_self]
  obtain ⟨w,hw⟩ := (acyclic_iff_cycles C).mp hC n x hxcycle
  refine ⟨z₂ + i.f (n+1) w,?_⟩
  rw [map_add,map_d_apply,hw,hx]
  abel

/-- The quotient in a degreewise short exact sequence is acyclic when the first
two complexes are. The degree-zero endpoint is handled explicitly. -/
theorem acyclic_quotient_of_shortExact (i : C ⟶ D) (p : D ⟶ E)
    (hinj : ∀ n, Function.Injective (i.f n))
    (hex : ∀ n, Function.Exact (i.f n) (p.f n))
    (hsurj : ∀ n, Function.Surjective (p.f n))
    (hC : C.Acyclic) (hD : D.Acyclic) : E.Acyclic := by
  apply (acyclic_iff_cycles E).mpr
  intro n z hz
  obtain ⟨y,hy⟩ := hsurj n z
  cases n with
  | zero =>
    have hcy : D.d 0 0 y = 0 := by rw [D.shape 0 0 (by simp)]; rfl
    obtain ⟨w,hw⟩ := (acyclic_iff_cycles D).mp hD 0 y hcy
    refine ⟨p.f 1 w,?_⟩
    rw [map_d_apply,hw,hy]
  | succ n =>
    have hpy : p.f n (D.d (n+1) n y) = 0 := by
      rw [← map_d_apply,hy]
      exact hz
    obtain ⟨x,hx⟩ := (hex n (D.d (n+1) n y)).mp hpy
    have hcx : C.d n (n-1) x = 0 := by
      apply hinj (n-1)
      rw [map_zero,← map_d_apply,hx]
      exact congrArg (fun f => f y) (D.d_comp_d (n+1) n (n-1))
    obtain ⟨t,ht⟩ := (acyclic_iff_cycles C).mp hC n x hcx
    have hycycle : D.d (n+1) n (y-i.f (n+1) t) = 0 := by
      rw [map_sub,map_d_apply,ht,hx,sub_self]
    obtain ⟨w,hw⟩ := (acyclic_iff_cycles D).mp hD (n+1) (y-i.f (n+1) t) hycycle
    refine ⟨p.f (n+2) w,?_⟩
    rw [map_d_apply,hw,map_sub,hy]
    have hpi := (hex (n+1) (i.f (n+1) t)).mpr ⟨t,rfl⟩
    rw [hpi,sub_zero]

/-- The subcomplex in a degreewise short exact sequence is acyclic when the
last two complexes are. -/
theorem acyclic_subcomplex_of_shortExact (i : C ⟶ D) (p : D ⟶ E)
    (hinj : ∀ n, Function.Injective (i.f n))
    (hex : ∀ n, Function.Exact (i.f n) (p.f n))
    (hsurj : ∀ n, Function.Surjective (p.f n))
    (hD : D.Acyclic) (hE : E.Acyclic) : C.Acyclic := by
  apply (acyclic_iff_cycles C).mpr
  intro n x hx
  have hix : D.d n (n-1) (i.f n x) = 0 := by rw [map_d_apply,hx,map_zero]
  obtain ⟨y,hy⟩ := (acyclic_iff_cycles D).mp hD n (i.f n x) hix
  have hpy : E.d (n+1) n (p.f (n+1) y) = 0 := by
    rw [map_d_apply,hy]
    exact (hex n (i.f n x)).mpr ⟨x,rfl⟩
  obtain ⟨z,hz⟩ := (acyclic_iff_cycles E).mp hE (n+1) (p.f (n+1) y) hpy
  obtain ⟨w,hw⟩ := hsurj (n+2) z
  have hpcorr : p.f (n+1) (y-D.d (n+2) (n+1) w) = 0 := by
    rw [map_sub,← map_d_apply,hw,hz,sub_self]
  obtain ⟨t,ht⟩ := (hex (n+1) (y-D.d (n+2) (n+1) w)).mp hpcorr
  refine ⟨t,?_⟩
  apply hinj n
  rw [← map_d_apply,ht,map_sub,hy]
  have hd := congrArg (fun f => f w) (D.d_comp_d (n+2) (n+1) n)
  change D.d (n+1) n (D.d (n+2) (n+1) w) = 0 at hd
  rw [hd,sub_zero]

end KhanSL2.Factorization.ComplexExactness