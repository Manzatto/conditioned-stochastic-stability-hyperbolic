module

public import LeanShared.Dynamics.IsolatingNeighborhood
public import LeanShared.Topology.PerturbationSeparation
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.Linarith

/-!
# Finite isolation and uniformly robust exit

These results use compactness and uniform continuity, without hyperbolicity.
The robustness assertions allow different, possibly discontinuous maps at
every time step; their error is required only while the orbit is in `K`.
-/

@[expose] public section

open Set Function Metric

namespace LeanShared

variable {X : Type*}

/-- Survival in `K` through the finite horizon `N`, including time zero. -/
def finiteForwardCore (f : X → X) (K : Set X) (N : ℕ) : Set X :=
  {x | ∀ n ≤ N, f^[n] x ∈ K}

/-- The orbit obtained by applying the map `F n` at time `n`. -/
def nonautonomousOrbit (F : ℕ → X → X) (x : X) : ℕ → X
  | 0 => x
  | n + 1 => F n (nonautonomousOrbit F x n)

@[simp] theorem nonautonomousOrbit_zero (F : ℕ → X → X) (x : X) :
    nonautonomousOrbit F x 0 = x := rfl

@[simp] theorem nonautonomousOrbit_succ (F : ℕ → X → X) (x : X) (n : ℕ) :
    nonautonomousOrbit F x (n + 1) = F n (nonautonomousOrbit F x n) := rfl

theorem antitone_finiteForwardCore (f : X → X) (K : Set X) :
    Antitone (finiteForwardCore f K) :=
  fun _ _ h _x hx n hn => hx n (hn.trans h)

theorem iInter_finiteForwardCore (f : X → X) (K : Set X) :
    (⋂ N, finiteForwardCore f K N) = forwardTrapped f K := by
  ext x
  constructor
  · intro hx n
    exact mem_iInter.mp hx n n le_rfl
  · intro hx
    exact mem_iInter.mpr fun _ n _ => hx n

section Topological

variable [TopologicalSpace X]

theorem isClosed_finiteForwardCore {f : X → X} {K : Set X}
    (hf : Continuous f) (hK : IsClosed K) (N : ℕ) :
    IsClosed (finiteForwardCore f K N) := by
  have heq : finiteForwardCore f K N = ⋂ n, ⋂ (_ : n ≤ N), f^[n] ⁻¹' K := by
    ext x
    simp [finiteForwardCore]
  rw [heq]
  exact isClosed_iInter fun n => isClosed_iInter fun _ => hK.preimage (hf.iterate n)

/-- A compact set disjoint from the forward-trapped set has a uniform,
positive finite exit horizon. Exit need not occur at the same time for every point. -/
theorem exists_pos_uniform_forward_exit [T2Space X] {f : X → X} {K C : Set X}
    (hf : Continuous f) (hK : IsClosed K) (hC : IsCompact C)
    (hdis : Disjoint C (forwardTrapped f K)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ C, ∃ n ≤ N, f^[n] x ∉ K := by
  classical
  let D : ℕ → Set X := fun N => C ∩ finiteForwardCore f K N
  have hD0 : IsCompact (D 0) := hC.inter_right (isClosed_finiteForwardCore hf hK 0)
  have hDclosed : ∀ N, IsClosed (D N) :=
    fun N => hC.isClosed.inter (isClosed_finiteForwardCore hf hK N)
  have hDanti : Antitone D := fun _ _ h =>
    inter_subset_inter (Subset.refl C) (antitone_finiteForwardCore f K h)
  have hcore : (⋂ N, D N) ⊆ (∅ : Set X) := by
    intro x hx
    exact (disjoint_left.mp hdis (mem_iInter.mp hx 0).1
      (fun n => (mem_iInter.mp hx n).2 n le_rfl)).elim
  obtain ⟨N, hN, hsub⟩ := exists_pos_tail_subset_open hD0 hDclosed hDanti isOpen_empty hcore
  refine ⟨N, hN, ?_⟩
  intro x hx
  by_contra hno
  have hsurvive : x ∈ finiteForwardCore f K N := by
    intro n hn
    by_contra hnk
    exact hno ⟨n, hn, hnk⟩
  exact hsub ⟨hx, hsurvive⟩

/-- Two-sided finite orbit segments eventually detect any open neighborhood
of the isolated core. -/
theorem exists_pos_finite_isolation [T2Space X] (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∀ x,
      (∀ n ≤ N, (T : X → X)^[n] x ∈ K) →
      (∀ n ≤ N, (T.symm : X → X)^[n] x ∈ K) → x ∈ U := by
  let D : ℕ → Set X := fun N =>
    finiteForwardCore T K N ∩ finiteForwardCore T.symm K N
  have hDclosed : ∀ N, IsClosed (D N) := fun N =>
    (isClosed_finiteForwardCore T.continuous hK.isClosed N).inter
      (isClosed_finiteForwardCore T.symm.continuous hK.isClosed N)
  have hD0 : IsCompact (D 0) := hK.of_isClosed_subset (hDclosed 0)
    (fun _ hx => hx.1 0 le_rfl)
  have hDanti : Antitone D := fun _ _ h => inter_subset_inter
    (antitone_finiteForwardCore T K h) (antitone_finiteForwardCore T.symm K h)
  have hDcore : (⋂ N, D N) ⊆ U := by
    intro x hx
    exact hcore ⟨fun n => (mem_iInter.mp hx n).1 n le_rfl,
      fun n => (mem_iInter.mp hx n).2 n le_rfl⟩
  obtain ⟨N, hN, hsub⟩ := exists_pos_tail_subset_open hD0 hDclosed hDanti hU hDcore
  exact ⟨N, hN, fun _ hf hb => hsub ⟨hf, hb⟩⟩

end Topological

section Metric

variable [MetricSpace X]

/-- At a fixed finite horizon, small one-step errors uniformly control the
whole orbit segment. Different maps can generate each step. -/
theorem exists_uniform_finite_orbit_closeness {f : X → X} (hf : UniformContinuous f)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ → X,
      (∀ n < N, dist (z (n + 1)) (f (z n)) < δ) →
      ∀ n ≤ N, dist (z n) (f^[n] (z 0)) < ε := by
  induction N generalizing ε with
  | zero =>
      refine ⟨1, zero_lt_one, ?_⟩
      intro z _ n hn
      have : n = 0 := Nat.eq_zero_of_le_zero hn
      simpa [this] using hε
  | succ N ih =>
      obtain ⟨γ, hγ, huc⟩ := Metric.uniformContinuous_iff.mp hf (ε / 2) (by linarith)
      obtain ⟨δ, hδ, hprev⟩ := ih (ε := min (ε / 2) γ) (lt_min (by linarith) hγ)
      refine ⟨min δ (ε / 2), lt_min hδ (by linarith), ?_⟩
      intro z hstep n hn
      have hprefix : ∀ m ≤ N, dist (z m) (f^[m] (z 0)) < min (ε / 2) γ :=
        hprev z (fun m hm => (hstep m (hm.trans (Nat.lt_succ_self N))).trans_le
          (min_le_left _ _))
      by_cases hle : n ≤ N
      · exact (hprefix n hle).trans_le (by linarith [min_le_left (ε / 2) γ])
      · have hnlast : n = N + 1 := by omega
        rw [hnlast, Function.iterate_succ_apply']
        have hfirst : dist (z (N + 1)) (f (z N)) < ε / 2 :=
          (hstep N (Nat.lt_succ_self N)).trans_le (min_le_right _ _)
        have hsecond : dist (f (z N)) (f (f^[N] (z 0))) < ε / 2 :=
          huc ((hprefix N le_rfl).trans_le (min_le_right _ _))
        exact (dist_triangle _ _ _).trans_lt (by linarith)

/-- Finitely many continuous observations detecting exit from a closed set
have a common positive tolerance on a compact source set. -/
theorem exists_uniform_finite_observation_margin {J : Type*} [Fintype J]
    {C K : Set X} (hC : IsCompact C) (hK : IsClosed K) (q : J → X → X)
    (hq : ∀ i, Continuous (q i)) (hexit : ∀ x ∈ C, ∃ i, q i x ∉ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ C, ∀ z : J → X,
      (∀ i, dist (z i) (q i x) < ε) → ∃ i, z i ∉ K := by
  classical
  let Q : X → (J → X) := fun x i => q i x
  let S : Set (J → X) := {z | ∀ i, z i ∈ K}
  have hS : IsClosed S := by
    have heq : S = ⋂ i, (fun z : J → X => z i) ⁻¹' K := by
      ext z
      simp [S]
    rw [heq]
    exact isClosed_iInter fun i => hK.preimage (continuous_apply i)
  have hQC : IsCompact (Q '' C) := hC.image (continuous_pi hq)
  have hsub : Q '' C ⊆ Sᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hbad
    obtain ⟨i, hi⟩ := hexit x hx
    exact hi (hbad i)
  obtain ⟨ε, hε, hthick⟩ := hQC.exists_thickening_subset_open hS.isOpen_compl hsub
  refine ⟨ε, hε, ?_⟩
  intro x hx z hclose
  have hnot : z ∉ S := hthick (Metric.mem_thickening_iff.mpr
    ⟨Q x, ⟨x, hx, rfl⟩, (dist_pi_lt_iff hε).mpr hclose⟩)
  exact not_forall.mp hnot

/-- Uniformly close arbitrary finite sequences preserve bounded exit times.
The one-step estimate is needed only until the trajectory first exits `K`. -/
theorem exists_pos_robust_forward_exit {f : X → X} {K C : Set X}
    (hf : UniformContinuous f) (hK : IsClosed K) (hC : IsCompact C)
    (hdis : Disjoint C (forwardTrapped f K)) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ → X,
      z 0 ∈ C →
      (∀ n < N, z n ∈ K → dist (z (n + 1)) (f (z n)) < δ) →
      ∃ n ≤ N, z n ∉ K := by
  classical
  obtain ⟨N, hN, hexit⟩ := exists_pos_uniform_forward_exit hf.continuous hK hC hdis
  obtain ⟨ε, hε, hmargin⟩ := exists_uniform_finite_observation_margin hC hK
    (fun i : Fin (N + 1) => f^[i.val]) (fun i => hf.continuous.iterate i.val)
    (fun x hx => by
      obtain ⟨n, hn, hnk⟩ := hexit x hx
      exact ⟨⟨n, Nat.lt_succ_of_le hn⟩, hnk⟩)
  obtain ⟨δ, hδ, hclose⟩ := exists_uniform_finite_orbit_closeness hf N hε
  refine ⟨N, hN, δ, hδ, ?_⟩
  intro z hz hstep
  by_contra hno
  have hsurvive : ∀ n ≤ N, z n ∈ K := by
    intro n hn
    by_contra hnk
    exact hno ⟨n, hn, hnk⟩
  have hsegment := hclose z (fun n hn => hstep n hn (hsurvive n hn.le))
  obtain ⟨i, hi⟩ := hmargin (z 0) hz (fun i => z i.val)
    (fun i => hsegment i.val (Nat.le_of_lt_succ i.isLt))
  exact hi (hsurvive i.val (Nat.le_of_lt_succ i.isLt))

/-- Uniform bounded exit for arbitrary sequences of maps uniformly close on
`K`. No continuity or probability law is assumed for the perturbations. -/
theorem exists_pos_robust_exit_for_map_sequences {f : X → X} {K C : Set X}
    (hf : UniformContinuous f) (hK : IsClosed K) (hC : IsCompact C)
    (hdis : Disjoint C (forwardTrapped f K)) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℕ → X → X,
      (∀ n < N, ∀ y ∈ K, dist (F n y) (f y) < δ) →
      ∀ x ∈ C, ∃ n ≤ N, nonautonomousOrbit F x n ∉ K := by
  obtain ⟨N, hN, δ, hδ, hexit⟩ := exists_pos_robust_forward_exit hf hK hC hdis
  refine ⟨N, hN, δ, hδ, ?_⟩
  intro F hF x hx
  exact hexit (nonautonomousOrbit F x) hx (fun n hn hy => hF n hn _ hy)

/-- The random finite-isolation statement: if both forward and backward
pseudo-orbits survive in `K`, their common middle point belongs to `U`. -/
theorem exists_pos_robust_finite_isolation (T : X ≃ₜ X) {K U : Set X}
    (hT : UniformContinuous (T : X → X)) (hTi : UniformContinuous (T.symm : X → X))
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℕ → X,
      a 0 = b 0 →
      (∀ n ≤ N, a n ∈ K) → (∀ n ≤ N, b n ∈ K) →
      (∀ n < N, dist (a (n + 1)) (T (a n)) < δ) →
      (∀ n < N, dist (b (n + 1)) (T.symm (b n)) < δ) → a 0 ∈ U := by
  classical
  obtain ⟨N, hN, hisolate⟩ := exists_pos_finite_isolation T hK hU hcore
  let q : Bool × Fin (N + 1) → X → X := fun i =>
    if i.1 then (T : X → X)^[i.2.val] else (T.symm : X → X)^[i.2.val]
  have hq : ∀ i, Continuous (q i) := by
    rintro ⟨flag, n⟩
    cases flag
    · exact T.symm.continuous.iterate n.val
    · exact T.continuous.iterate n.val
  have hexit : ∀ x ∈ K \ U, ∃ i, q i x ∉ K := by
    intro x hx
    by_contra hno
    have hall : ∀ i, q i x ∈ K := by
      intro i
      by_contra hi
      exact hno ⟨i, hi⟩
    apply hx.2
    apply hisolate x
    · intro n hn
      simpa only [q, ↓reduceIte] using hall (true, ⟨n, Nat.lt_succ_of_le hn⟩)
    · intro n hn
      simpa only [q, Bool.false_eq_true, ↓reduceIte] using
        hall (false, ⟨n, Nat.lt_succ_of_le hn⟩)
  obtain ⟨ε, hε, hmargin⟩ := exists_uniform_finite_observation_margin (hK.diff hU)
    hK.isClosed q hq hexit
  obtain ⟨δa, hδa, hca⟩ := exists_uniform_finite_orbit_closeness hT N hε
  obtain ⟨δb, hδb, hcb⟩ := exists_uniform_finite_orbit_closeness hTi N hε
  refine ⟨N, hN, min δa δb, lt_min hδa hδb, ?_⟩
  intro a b hab ha hb hsa hsb
  by_contra hout
  let z : Bool × Fin (N + 1) → X := fun i => if i.1 then a i.2.val else b i.2.val
  have hclose : ∀ i, dist (z i) (q i (a 0)) < ε := by
    rintro ⟨flag, n⟩
    cases flag
    · change dist (b n.val) ((T.symm : X → X)^[n.val] (a 0)) < ε
      rw [hab]
      exact hcb b (fun n hn => (hsb n hn).trans_le (min_le_right _ _))
        n.val (Nat.le_of_lt_succ n.isLt)
    · exact hca a (fun n hn => (hsa n hn).trans_le (min_le_left _ _))
        n.val (Nat.le_of_lt_succ n.isLt)
  obtain ⟨i, hi⟩ := hmargin (a 0) ⟨ha 0 (Nat.zero_le N), hout⟩ z hclose
  rcases i with ⟨flag, n⟩
  apply hi
  cases flag
  · exact hb n.val (Nat.le_of_lt_succ n.isLt)
  · exact ha n.val (Nat.le_of_lt_succ n.isLt)

end Metric

end LeanShared
