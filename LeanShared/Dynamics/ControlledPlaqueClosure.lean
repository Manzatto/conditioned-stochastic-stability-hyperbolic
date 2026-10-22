module

public import LeanShared.Dynamics.BackwardIsolation
public import Mathlib.Logic.Relation
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Truncated-past plaques and controlled reachability

Plaque continuity and live backward plaque orbits are explicit classical
hyperbolic inputs. Plaque inclusion in controlled reachability closure is a
conclusion. Deterministic tails approach the isolated core using compactness;
the reachable collar is fixed at the chosen noise size. A later geometric
capture neighborhood is separate from this collar.
-/

@[expose] public noncomputable section

open Set Function Filter
open scoped Topology

namespace LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*}

def liveStep (F : X × Ω → X) (V : Set X) (x y : X) : Prop :=
  x ∈ V ∧ y ∈ V ∧ ∃ ω : Ω, F (x, ω) = y

/-- Actual finite controls, with every source and arrival inside the live interior. -/
def reachable (F : X × Ω → X) (V A : Set X) : Set X :=
  {y | ∃ x ∈ A, x ∈ V ∧ Relation.ReflTransGen (liveStep F V) x y}

theorem reachable_subset_live (F : X × Ω → X) (V A : Set X) : reachable F V A ⊆ V := by
  rintro y ⟨x, _, hxV, hp⟩
  induction hp with
  | refl => exact hxV
  | tail _ hstep _ => exact hstep.2.1

theorem core_mem_reachable (F : X × Ω → X) (V A : Set X) {x : X}
    (hx : x ∈ A) (hxV : x ∈ V) : x ∈ reachable F V A := ⟨x, hx, hxV, .refl⟩

theorem reachable_step (F : X × Ω → X) (V A : Set X) {x y : X}
    (hx : x ∈ reachable F V A) (hy : y ∈ V) (ω : Ω) (hstep : F (x, ω) = y) :
    y ∈ reachable F V A := by
  have hxV := reachable_subset_live F V A hx
  obtain ⟨a, ha, haV, hpath⟩ := hx
  exact ⟨a, ha, haV, hpath.tail ⟨hxV, hy, ω, hstep⟩⟩

/-- A reachable backward iterate returns by its actual finite live control segment. -/
theorem reachable_of_backward_iterate (F : X × Ω → X) (V A : Set X)
    (z : ℕ → X) (noise : ℕ → Ω) (hz : ∀ n, z n ∈ V)
    (hstep : ∀ n, F (z (n + 1), noise n) = z n) (N : ℕ)
    (hN : z N ∈ reachable F V A) : z 0 ∈ reachable F V A := by
  induction N with
  | zero => exact hN
  | succ N ih =>
      exact ih (reachable_step F V A hN (hz N) (noise N) (hstep N))

def truncatedPast (zero : Ω) (ω : ℤ → Ω) (k : ℕ) (i : ℤ) : Ω :=
  if i < -(k : ℤ) then zero else ω i

def backwardNoise (ω : ℤ → Ω) (n : ℕ) : Ω := ω (-(n : ℤ) - 1)

theorem backwardNoise_truncatedPast (zero : Ω) (ω : ℤ → Ω) {k n : ℕ} (hkn : k ≤ n) :
    backwardNoise (truncatedPast zero ω k) n = zero := by
  unfold backwardNoise truncatedPast
  rw [ite_eq_left (by omega)]

variable [TopologicalSpace Ω]

/-- The literal truncations converge in the product topology. -/
theorem truncatedPast_tendsto (zero : Ω) (ω : ℤ → Ω) :
    Tendsto (truncatedPast zero ω) atTop (𝓝 ω) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have heq : (fun k => truncatedPast zero ω k i) =ᶠ[atTop] (fun _ => ω i) := by
    filter_upwards [eventually_ge_atTop (-i).toNat] with k hk
    exact ite_eq_right (by omega)
  exact tendsto_const_nhds.congr' heq.symm

variable [MetricSpace X]

omit [TopologicalSpace Ω] in
/-- The local submersion image hypothesis produces an open reachable collar
at the chosen noise size. No uniform radius or zero region is assumed. -/
theorem exists_open_reachable_neighborhood (T : X ≃ₜ X) (F : X × Ω → X) (V K : Set X)
    (hcoreV : isolatedCore T K ⊆ V)
    (hcover : ∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
      ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y) :
    ∃ W : Set X, IsOpen W ∧ isolatedCore T K ⊆ W ∧ W ⊆ reachable F V (isolatedCore T K) := by
  let W : isolatedCore T K → Set X := fun p => (hcover p p.property).choose
  have hW (p : isolatedCore T K) : IsOpen (W p) ∧ (p : X) ∈ W p ∧ W p ⊆ V ∧
      ∀ y ∈ W p, ∃ ω : Ω, F (T.symm p, ω) = y := (hcover p p.property).choose_spec
  refine ⟨⋃ p, W p, isOpen_iUnion fun p => (hW p).1, ?_, ?_⟩
  · intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, (hW ⟨p, hp⟩).2.1⟩
  · intro y hy
    obtain ⟨p, hyp⟩ := mem_iUnion.mp hy
    obtain ⟨ω, hω⟩ := (hW p).2.2.2 y hyp
    have hx := mapsTo_isolatedCore_symm T K p.property
    exact reachable_step F V _ (core_mem_reachable F V _ hx (hcoreV hx))
      ((hW p).2.2.1 hyp) ω hω

/-- A contained backward orbit with an eventually deterministic past enters
any open neighborhood of the isolated core. No random closeness estimate is used. -/
theorem deterministic_backward_tail_enters (T : X ≃ₜ X) {K W : Set X}
    (hK : IsCompact K) (hW : IsOpen W) (hcore : isolatedCore T K ⊆ W)
    (z : ℕ → X) (hz : ∀ n, z n ∈ K) (k : ℕ)
    (hdet : ∀ n, k ≤ n → T (z (n + 1)) = z n) : ∃ n : ℕ, z n ∈ W := by
  have heq : ∀ j : ℕ, z (k + j) = (T.symm : X → X)^[j] (z k) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hs := congrArg T.symm (hdet (k + j) (Nat.le_add_right k j))
        simpa only [T.symm_apply_apply, Nat.succ_eq_add_one, Nat.add_assoc,
          iterate_succ_apply', ih] using hs
  have ht : z k ∈ forwardTrapped T.symm K := by
    intro j
    rw [← heq j]
    exact hz _
  have hcore' : isolatedCore T.symm K ⊆ W := by
    simpa only [isolatedCore, Homeomorph.symm_symm, inter_comm] using hcore
  obtain ⟨N, _, hN⟩ := exists_pos_stable_tail_subset T.symm hK hW hcore'
  refine ⟨k + N, ?_⟩
  rw [heq N]
  exact hN ⟨z k, ht, rfl⟩

/-- Step 2: lower semicontinuity of genuine plaques, their contained backward
orbits, and the fixed-noise local images imply plaque closure reachability. -/
theorem plaque_subset_closure_reachable (T : X ≃ₜ X) (F : X × Ω → X) (zero : Ω)
    (hzero : ∀ x, F (x, zero) = T x) (V K : Set X) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : isolatedCore T K ⊆ V)
    (hcover : ∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
      ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y)
    (plaque : (ℤ → Ω) → Set X)
    (hlsc : ∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
      ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧ ∀ k, zn k ∈ plaque (ωn k))
    (hback : ∀ ω : ℤ → Ω, ∀ z ∈ plaque ω, ∃ b : ℕ → X, b 0 = z ∧
      (∀ n, b n ∈ V) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n) :
    ∀ ω : ℤ → Ω, plaque ω ⊆ closure (reachable F V (isolatedCore T K)) := by
  obtain ⟨W, hW, hcoreW, hWreach⟩ := exists_open_reachable_neighborhood T F V K hcoreV hcover
  intro ω z hz
  obtain ⟨zn, hlim, hzn⟩ := hlsc ω (truncatedPast zero ω) (truncatedPast_tendsto zero ω) z hz
  apply mem_closure_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  obtain ⟨b, hb0, hbV, hbstep⟩ := hback _ _ (hzn k)
  have hdet : ∀ n, k ≤ n → T (b (n + 1)) = b n := by
    intro n hn
    have hs := hbstep n
    rw [backwardNoise_truncatedPast zero ω hn, hzero] at hs
    exact hs
  obtain ⟨n, hn⟩ := deterministic_backward_tail_enters T hK hW hcoreW b (fun n => hVK (hbV n)) k hdet
  have hbReach := reachable_of_backward_iterate F V _ b _ hbV hbstep n (hWreach hn)
  rwa [hb0] at hbReach

/-- The ordinary forward-density formulation of transitivity on an invariant set. -/
def forwardTransitiveOn (T : X → X) (A : Set X) : Prop :=
  ∀ W : Set X, IsOpen W → (A ∩ W).Nonempty → A ⊆ closure (⋃ n : ℕ, T^[n] '' (A ∩ W))

omit [TopologicalSpace Ω] in
/-- Step 1: one core zero and the local noise images force zero on the whole
transitive core. Only continuity on the compact isolating region is needed. -/
theorem zero_on_core_of_zero (T : X ≃ₜ X) (F : X × Ω → X) (zero : Ω)
    (hFzero : ∀ x, F (x, zero) = T x) (V K : Set X)
    (hcoreV : isolatedCore T K ⊆ V)
    (hcover : ∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
      ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y)
    (htrans : forwardTransitiveOn T (isolatedCore T K))
    (g : X → ℝ) (hgc : ContinuousOn g K)
    (hzeroStep : ∀ x ∈ K, ∀ ω : Ω, F (x, ω) ∈ V → g x = 0 → g (F (x, ω)) = 0)
    {x : X} (hx : x ∈ isolatedCore T K) (hgx : g x = 0) :
    EqOn g (fun _ => 0) (isolatedCore T K) := by
  have hcoreK : isolatedCore T K ⊆ K := fun _ hy => forwardTrapped_subset T K hy.1
  obtain ⟨W, hW, hpW, hWV, hnoise⟩ := hcover (T x) (mapsTo_isolatedCore T K hx)
  have hgW : ∀ y ∈ W, g y = 0 := by
    intro y hy
    obtain ⟨ω, hω⟩ := hnoise y hy
    rw [T.symm_apply_apply] at hω
    have hh := hzeroStep x (hcoreK hx) ω (hω.symm ▸ hWV hy) hgx
    rwa [hω] at hh
  have hforward : ∀ a ∈ isolatedCore T K, g a = 0 → ∀ n : ℕ, g ((T : X → X)^[n] a) = 0 := by
    intro a ha hga n
    induction n with
    | zero => exact hga
    | succ n ih =>
        have hn := iterate_mem_isolatedCore T K ha n
        have hTn := mapsTo_isolatedCore T K hn
        have hh := hzeroStep _ (hcoreK hn) zero (by rw [hFzero]; exact hcoreV hTn) ih
        simpa only [hFzero, iterate_succ_apply'] using hh
  let D : Set X := ⋃ n : ℕ, (T : X → X)^[n] '' (isolatedCore T K ∩ W)
  have hDcore : D ⊆ isolatedCore T K := by
    intro y hy
    obtain ⟨n, a, ha, rfl⟩ := mem_iUnion.mp hy
    exact iterate_mem_isolatedCore T K ha.1 n
  have hgD : EqOn g (fun _ => 0) D := by
    intro y hy
    obtain ⟨n, a, ha, rfl⟩ := mem_iUnion.mp hy
    exact hforward a ha.1 (hgW a ha.2) n
  exact hgD.of_subset_closure (hgc.mono hcoreK) continuousOn_const hDcore
    (htrans W hW ⟨T x, mapsTo_isolatedCore T K hx, hpW⟩)

omit [TopologicalSpace Ω] in
/-- Controlled zero propagation extends to the ambient closure of the actual
reachable set, while all continuity is confined to the compact region `K`. -/
theorem zero_on_closure_reachable (F : X × Ω → X) (V K A : Set X)
    (hVK : V ⊆ K) (hK : IsClosed K) (g : X → ℝ) (hgc : ContinuousOn g K)
    (hA : EqOn g (fun _ => 0) A)
    (hzeroStep : ∀ x ∈ K, ∀ ω : Ω, F (x, ω) ∈ V → g x = 0 → g (F (x, ω)) = 0) :
    EqOn g (fun _ => 0) (closure (reachable F V A)) := by
  have hreach : EqOn g (fun _ => 0) (reachable F V A) := by
    rintro y ⟨a, ha, _, hp⟩
    induction hp with
    | refl => exact hA ha
    | @tail b c hp hstep ih =>
        obtain ⟨ω, hω⟩ := hstep.2.2
        have hh := hzeroStep b (hVK hstep.1) ω (hω.symm ▸ hstep.2.1) ih
        rwa [hω] at hh
  have hclosureK : closure (reachable F V A) ⊆ K :=
    closure_minimal ((reachable_subset_live F V A).trans hVK) hK
  exact hreach.of_subset_closure (hgc.mono hclosureK) continuousOn_const subset_closure (Subset.refl _)

omit [TopologicalSpace Ω] [MetricSpace X] in
/-- Exact support parents and zero propagation construct a positive backward
orbit. The live-interior condition applies only to positive supported points. -/
theorem exists_positive_backward_orbit (F : X × Ω → X) (V K S : Set X)
    (hSK : S ⊆ K) (g : X → ℝ) (hg0 : ∀ x ∈ K, 0 ≤ g x)
    (hpositiveLive : ∀ x ∈ S, 0 < g x → x ∈ V)
    (hzeroStep : ∀ x ∈ K, ∀ ω : Ω, F (x, ω) ∈ V → g x = 0 → g (F (x, ω)) = 0)
    (hparent : ∀ p ∈ S, ∃ x ∈ S, ∃ ω : Ω, F (x, ω) = p)
    (p : X) (hp : p ∈ S) (hgp : 0 < g p) :
    ∃ z : ℕ → X, ∃ noise : ℕ → Ω, z 0 = p ∧
      (∀ n, z n ∈ S ∧ z n ∈ V ∧ 0 < g (z n)) ∧
      ∀ n, F (z (n + 1), noise n) = z n := by
  let P := {x : X // x ∈ S ∧ 0 < g x}
  have hpp : ∀ q : P, ∃ a : P, ∃ ω : Ω, F ((a : X), ω) = (q : X) := by
    intro q
    obtain ⟨a, ha, ω, hω⟩ := hparent q q.property.1
    have hga : 0 < g a := by
      by_contra hbad
      have hga0 : g a = 0 := le_antisymm (le_of_not_gt hbad) (hg0 a (hSK ha))
      have hh := hzeroStep a (hSK ha) ω
        (hω.symm ▸ hpositiveLive q q.property.1 q.property.2) hga0
      rw [hω] at hh
      exact (ne_of_gt q.property.2) hh
    exact ⟨⟨a, ha, hga⟩, ω, hω⟩
  let parent : P → P := fun q => (hpp q).choose
  have hnoise (q : P) : ∃ ω : Ω, F (((parent q : P) : X), ω) = (q : X) := (hpp q).choose_spec
  let a : ℕ → P := fun n => parent^[n] ⟨p, hp, hgp⟩
  refine ⟨fun n => (a n : X), fun n => (hnoise (a n)).choose, rfl,
    (fun n => ⟨(a n).property.1, hpositiveLive _ (a n).property.1 (a n).property.2, (a n).property.2⟩), ?_⟩
  intro n
  have he : a (n + 1) = parent (a n) := iterate_succ_apply' parent n _
  change F ((a (n + 1) : X), (hnoise (a n)).choose) = (a n : X)
  rw [he]
  exact (hnoise (a n)).choose_spec

/-- Localization of the positive product discharges the live-interior
condition for positive supported points. It uses continuity only on `K` and
does not assume positivity anywhere on the isolated core. -/
theorem positive_supported_mem_live (K V S : Set X) (hSK : S ⊆ K)
    (g m : X → ℝ) (hgc : ContinuousOn g K)
    (hS : S ⊆ closure {y | y ∈ K ∧ 0 < m y})
    (hproduct : closure {y | y ∈ K ∧ 0 < g y * m y} ⊆ V)
    {x : X} (hx : x ∈ S) (hgx : 0 < g x) : x ∈ V := by
  have hevent : {y | 0 < g y} ∈ 𝓝[K] x := (hgc x (hSK hx)) (lt_mem_nhds hgx)
  obtain ⟨O, hO, hOg⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hevent
  obtain ⟨W, hWO, hW, hxW⟩ := mem_nhds_iff.mp hO
  have hxclosure : x ∈ closure (W ∩ {y | y ∈ K ∧ 0 < m y}) := hW.inter_closure ⟨hxW, hS hx⟩
  apply hproduct
  apply closure_mono _ hxclosure
  rintro y ⟨hyW, hyK, hym⟩
  exact ⟨hyK, mul_pos (hOg ⟨hWO hyW, hyK⟩) hym⟩

def completeBackwardNoise (zero : Ω) (noise : ℕ → Ω) (i : ℤ) : Ω :=
  if i < 0 then noise ((-i - 1).toNat) else zero

omit [TopologicalSpace Ω] in
theorem backwardNoise_complete (zero : Ω) (noise : ℕ → Ω) (n : ℕ) :
    backwardNoise (completeBackwardNoise zero noise) n = noise n := by
  unfold backwardNoise completeBackwardNoise
  rw [ite_eq_left (by omega)]
  congr 1
  omega

def backwardShift (ω : ℤ → Ω) (j : ℕ) (i : ℤ) : Ω := ω (i - (j : ℤ))

variable [CompactSpace X]

/-- Steps 1--3 with a noncircular noise threshold. The geometric neighborhood
`G` is chosen before the threshold, maps, eigenfunction, and reachable collar.
Classical local unstable capture is conditional only on the derived tail in
`G`; neither plaque reachability nor core positivity is an input.

The set `S` can be the actual left eigenmeasure support. Its exact parents
come from `NoiseEigenmeasureSupport`; the positive-supported-live condition
comes from localization of the quasi-ergodic measure, and the positive seed
comes from its normalization. -/
theorem exists_pos_noise_tolerance_for_core_positivity (T : X ≃ₜ X) (V K G : Set X)
    (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (zero : Ω),
      (∀ x, F (x, zero) = T x) →
      (∀ ω : Ω, ∀ x ∈ K, dist (F (x, ω)) (T x) < δ) →
      (∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
        ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y) →
      ∀ plaque : (ℤ → Ω) → Set X,
      (∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
        ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧ ∀ k, zn k ∈ plaque (ωn k)) →
      (∀ ω : ℤ → Ω, ∀ z ∈ plaque ω, ∃ b : ℕ → X, b 0 = z ∧
        (∀ n, b n ∈ V) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
      (∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
        (∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
        (∀ᶠ n : ℕ in atTop, b n ∈ G) → ∃ j : ℕ, b j ∈ plaque (backwardShift ω j)) →
      ∀ (g : X → ℝ), ContinuousOn g K → (∀ x ∈ K, 0 ≤ g x) →
      (∀ x ∈ K, ∀ ω : Ω, F (x, ω) ∈ V → g x = 0 → g (F (x, ω)) = 0) →
      ∀ S : Set X, S ⊆ K → (∀ x ∈ S, 0 < g x → x ∈ V) →
      (∀ p ∈ S, ∃ x ∈ S, ∃ ω : Ω, F (x, ω) = p) →
      (∃ p ∈ S, 0 < g p) → ∀ x ∈ isolatedCore T K, 0 < g x := by
  obtain ⟨N, _, δ, hδ, htail⟩ := exists_pos_backward_tail_isolation_of_compact T hK hG hcoreG
  refine ⟨δ, hδ, ?_⟩
  intro F zero hFzero hnoise hcover plaque hlsc hback hcapture g hgc hg0 hzeroStep S hSK hpositiveLive hparent hseed
  have hplaque := plaque_subset_closure_reachable T F zero hFzero V K hVK hK hcoreV hcover plaque hlsc hback
  obtain ⟨p, hp, hgp⟩ := hseed
  obtain ⟨z, noise, _hz0, hz, hstep⟩ :=
    exists_positive_backward_orbit F V K S hSK g hg0 hpositiveLive hzeroStep hparent p hp hgp
  let ω : ℤ → Ω := completeBackwardNoise zero noise
  have hstep' : ∀ n, F (z (n + 1), backwardNoise ω n) = z n := by
    intro n
    simpa only [ω, backwardNoise_complete] using hstep n
  have herr : ∀ n, dist (T (z (n + 1))) (z n) < δ := by
    intro n
    rw [← hstep n, dist_comm]
    exact hnoise (noise n) _ (hSK (hz (n + 1)).1)
  have hGtail : ∀ᶠ n : ℕ in atTop, z n ∈ G :=
    eventually_atTop.mpr ⟨N, fun n hn => htail z (fun j => hSK (hz j).1) herr n hn⟩
  obtain ⟨j, hj⟩ := hcapture ω z (fun n => (hz n).2.1) hstep' hGtail
  intro x hx
  by_contra hbad
  have hgx : g x = 0 := le_antisymm (le_of_not_gt hbad)
    (hg0 x (forwardTrapped_subset T K hx.1))
  have hcoreZero := zero_on_core_of_zero T F zero hFzero V K hcoreV hcover htrans g hgc hzeroStep hx hgx
  have hreachZero := zero_on_closure_reachable F V K _ hVK hK.isClosed g hgc hcoreZero hzeroStep
  exact (ne_of_gt (hz j).2.2) (hreachZero (hplaque (backwardShift ω j) hj))

end LeanShared.ControlledPlaqueClosure
