module

public import KhanSL2.Macdonald.StrongBridgeGenerators
public import KhanSL2.StrongMacdonald.SliceRing

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The free Macdonald map respects the three gradings needed to extract
symmetric coefficient degree and homological degree from total cohomology. -/
noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

open StrongMacdonald in
/-- Even derivation intertwining can be checked on the actual generators. -/
theorem strong_algHom_derivation_intertwining (F : StrongMacdonald.W →ₐ[ℂ] StrongMacdonald.W)
    (D T : Module.End ℂ StrongMacdonald.W)
    (hD : HomDer 0 D) (hT : HomDer 0 T)
    (hs : ∀ g, T (F (sig g)) = F (D (sig g)))
    (hp : ∀ g, T (F (StrongMacdonald.psi g)) = F (D (StrongMacdonald.psi g))) (u : StrongMacdonald.W) :
    T (F u) = F (D u) := by
  refine induction_gen (P := fun u => T (F u) = F (D u)) ?_ ?_ ?_ ?_ ?_ ?_ u
  · simp
  · rw [map_one, hT.map_one, hD.map_one, map_zero]
  · intro u v hu hv
    simp only [map_add, hu, hv]
  · intro c u hu
    simp only [map_smul, hu]
  · intro g u hu
    rw [map_mul, hT.zero_mul_apply, hs, hu, hD.zero_mul_apply, map_add, map_mul, map_mul]
  · intro g u hu
    rw [map_mul, hT.zero_mul_apply, hp, hu, hD.zero_mul_apply, map_add, map_mul, map_mul]

open StrongMacdonald in
/-- The colour-zero free subspace is preserved by every diagonal grading. -/
theorem strong_diagDer_projFull (a : StrongMacdonald.SMode → ℕ)
    (b : StrongMacdonald.PMode → ℕ) (u : StrongMacdonald.W) :
    diagDer a b (projFull u) = projFull (diagDer a b u) := by
  apply strong_algHom_derivation_intertwining projFull (diagDer a b) (diagDer a b)
    (homDer_diagDer _ _) (homDer_diagDer _ _)
  · intro g
    rw [diagDer_sig, map_smul, projFull_sig]
    split <;> simp [diagDer_sig]
  · intro g
    rw [diagDer_psi, map_smul, projFull_psi]
    split <;> simp [diagDer_psi]

/-- Number of exterior generators in the imported coordinate model. -/
def strongExteriorEuler : Module.End ℂ StrongMacdonald.W :=
  StrongMacdonald.diagDer (fun _ => 0) (fun _ => 1)

/-- The target symmetric degree of a free expression: two per even generator,
one per odd generator. -/
def strongFreeSymmetricEuler : Module.End ℂ StrongMacdonald.W :=
  StrongMacdonald.diagDer (fun _ => 2) (fun _ => 1)

open StrongMacdonald in
theorem strong_diagonal_Sgen (a b : ℕ) (n : ℕ) :
    diagDer (fun _ => a) (fun _ => b) (Sgen n) =
      ((2*a : ℕ) : ℂ) • Sgen n := by
  have hs (k : ℕ) (c : Fin 3) :
      IsEig (diagDer (fun _ => a) (fun _ => b)) (a : ℂ) (sigOf k c) :=
    diagDer_sig _ _ _
  unfold Sgen
  apply IsEig.sum
  intro k _hk
  apply IsEig.sum
  intro c _hc
  exact ((hs k c).mul (homDer_diagDer _ _).isDer (hs (n-k) c)).congr (by push_cast; ring)

open StrongMacdonald in
theorem strong_diagonal_Egen (a b : ℕ) (n : ℕ) :
    diagDer (fun _ => a) (fun _ => b) (Egen n) =
      ((a+b : ℕ) : ℂ) • Egen n := by
  have hs (k : ℕ) (c : Fin 3) :
      IsEig (diagDer (fun _ => a) (fun _ => b)) (a : ℂ) (sigOf k c) :=
    diagDer_sig _ _ _
  have hp (k : ℕ) (c : Fin 3) :
      IsEig (diagDer (fun _ => a) (fun _ => b)) (b : ℂ) (psiOf k c) :=
    diagDer_psi _ _ _
  unfold Egen
  apply IsEig.sum
  intro j _hj
  apply IsEig.sum
  intro c _hc
  apply IsEig.smul
  exact ((hs (n-1-j) c).mul (homDer_diagDer _ _).isDer (hp j c)).congr (by push_cast; rfl)

open StrongMacdonald in
theorem strong_Wt_Sgen (n : ℕ) : Wt (Sgen n) = (n : ℂ) • Sgen n := by
  unfold Sgen
  apply IsEig.sum
  intro k hk
  apply IsEig.sum
  intro a _
  apply ((eig_Wt_sigOf k a).mul homDer_Wt.isDer (eig_Wt_sigOf (n-k) a)).congr
  have hk' := Finset.mem_range.mp hk
  norm_cast
  omega

open StrongMacdonald in
theorem strong_Wt_Egen (n : ℕ) : Wt (Egen n) = (n : ℂ) • Egen n := by
  unfold Egen
  apply IsEig.sum
  intro j hj
  apply IsEig.sum
  intro a _
  apply IsEig.smul
  apply ((eig_Wt_sigOf (n-1-j) a).mul homDer_Wt.isDer (eig_Wt_psiOf j a)).congr
  rw [add_comm]
  exact weight_cast (Finset.mem_range.mp hj)

open StrongMacdonald in
/-- Loop weight is unchanged by the specified free-generator map. -/
theorem strong_Wt_Gmap (u : StrongMacdonald.W) : Wt (Gmap u) = Gmap (Wt u) := by
  apply strong_algHom_derivation_intertwining Gmap Wt Wt homDer_Wt homDer_Wt
  · intro g
    have hs : Wt (sig g) = (g.index : ℂ) • sig g := diagDer_sig _ _ _
    rw [hs, map_smul]
    simp only [Gmap, substW_sig, Gsig]
    split <;> simp [strong_Wt_Sgen]
  · intro g
    have hp : Wt (StrongMacdonald.psi g) = ((g.index+1 : ℕ) : ℂ) • StrongMacdonald.psi g := diagDer_psi _ _ _
    rw [hp, map_smul]
    simp only [Gmap, substW_psi, Gpsi]
    split
    · simp only [map_smul, strong_Wt_Egen]
      exact smul_comm _ _ _
    · simp

open StrongMacdonald in
/-- Free bidegree (r,q) maps to symmetric coefficient degree 2r+q. -/
theorem strong_Sd_Gmap (u : StrongMacdonald.W) :
    Sd (Gmap u) = Gmap (strongFreeSymmetricEuler u) := by
  apply strong_algHom_derivation_intertwining Gmap strongFreeSymmetricEuler Sd
    (homDer_diagDer _ _) homDer_Sd
  · intro g
    have hs : strongFreeSymmetricEuler (sig g) = (2 : ℂ) • sig g := diagDer_sig _ _ _
    rw [hs, map_smul]
    simp only [Gmap, substW_sig, Gsig]
    split <;> simp [Sd, strong_diagonal_Sgen]
  · intro g
    have hp : strongFreeSymmetricEuler (StrongMacdonald.psi g) = (1 : ℂ) • StrongMacdonald.psi g := by
      simpa only [strongFreeSymmetricEuler, Nat.cast_one] using
        diagDer_psi (fun _ => 2) (fun _ => 1) g
    rw [hp, one_smul]
    simp only [Gmap, substW_psi, Gpsi]
    split <;> simp [Sd, strong_diagonal_Egen]

open StrongMacdonald in
/-- Exterior degree agrees with the number of free odd generators. -/
theorem strong_exteriorEuler_Gmap (u : StrongMacdonald.W) :
    strongExteriorEuler (Gmap u) = Gmap (strongExteriorEuler u) := by
  apply strong_algHom_derivation_intertwining Gmap strongExteriorEuler strongExteriorEuler
    (homDer_diagDer _ _) (homDer_diagDer _ _)
  · intro g
    have hs : strongExteriorEuler (sig g) = (0 : ℂ) • sig g := by
      simpa only [strongExteriorEuler, Nat.cast_zero] using
        diagDer_sig (fun _ => 0) (fun _ => 1) g
    rw [hs, zero_smul, map_zero]
    simp only [Gmap, substW_sig, Gsig]
    split <;> simp [strongExteriorEuler, strong_diagonal_Sgen]
  · intro g
    have hp : strongExteriorEuler (StrongMacdonald.psi g) = (1 : ℂ) • StrongMacdonald.psi g := by
      simpa only [strongExteriorEuler, Nat.cast_one] using
        diagDer_psi (fun _ => 0) (fun _ => 1) g
    rw [hp, one_smul]
    simp only [Gmap, substW_psi, Gpsi]
    split <;> simp [strongExteriorEuler, strong_diagonal_Egen]

end KhanSL2.Macdonald
