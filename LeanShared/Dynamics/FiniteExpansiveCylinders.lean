module

public import LeanShared.Dynamics.IsolatingNeighborhood
public import Mathlib.Topology.MetricSpace.Closeds

/-! Small itinerary sets are genuinely generating near a compact isolated
expansive core. The proof uses paired finite orbits and compactness; it does
not assume a generating property of an arbitrary finite atlas. -/

@[expose] public section
open Set Function
namespace LeanShared.FiniteExpansiveCylinders
variable {X : Type*} [MetricSpace X]

def window (T : X ≃ₜ X) (K : Set X) (c : ℝ) (n : ℕ) : Set (X × X) :=
  {z | ∀ j ≤ n,
    (T : X → X)^[j] z.1 ∈ K ∧ (T : X → X)^[j] z.2 ∈ K ∧
    dist ((T : X → X)^[j] z.1) ((T : X → X)^[j] z.2) ≤ c ∧
    (T.symm : X → X)^[j] z.1 ∈ K ∧ (T.symm : X → X)^[j] z.2 ∈ K ∧
    dist ((T.symm : X → X)^[j] z.1) ((T.symm : X → X)^[j] z.2) ≤ c}

theorem window_closed (T : X ≃ₜ X) {K : Set X} (hK : IsClosed K) (c : ℝ) (n : ℕ) :
    IsClosed (window T K c n) := by
  have heq : window T K c n = ⋂ j : ℕ, ⋂ (_ : j ≤ n),
      {z : X × X | (T : X → X)^[j] z.1 ∈ K} ∩
      {z : X × X | (T : X → X)^[j] z.2 ∈ K} ∩
      {z : X × X | dist ((T : X → X)^[j] z.1) ((T : X → X)^[j] z.2) ≤ c} ∩
      {z : X × X | (T.symm : X → X)^[j] z.1 ∈ K} ∩
      {z : X × X | (T.symm : X → X)^[j] z.2 ∈ K} ∩
      {z : X × X | dist ((T.symm : X → X)^[j] z.1) ((T.symm : X → X)^[j] z.2) ≤ c} := by
    ext z
    simp only [window, mem_ofPred_eq, mem_iInter, mem_inter_iff]
    aesop
  rw [heq]
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact (((((hK.preimage ((T.continuous.iterate j).comp continuous_fst)).inter
    (hK.preimage ((T.continuous.iterate j).comp continuous_snd))).inter
    (isClosed_le (((T.continuous.iterate j).comp continuous_fst).dist
      ((T.continuous.iterate j).comp continuous_snd)) continuous_const)).inter
    (hK.preimage ((T.symm.continuous.iterate j).comp continuous_fst))).inter
    (hK.preimage ((T.symm.continuous.iterate j).comp continuous_snd))).inter
    (isClosed_le (((T.symm.continuous.iterate j).comp continuous_fst).dist
      ((T.symm.continuous.iterate j).comp continuous_snd)) continuous_const)

theorem window_antitone (T : X ≃ₜ X) (K : Set X) (c : ℝ) :
    Antitone (window T K c) := by
  intro n m hnm z hz j hj
  exact hz j (hj.trans hnm)

/-- Expansivity only on the isolated core gives a uniform finite separation
criterion on all surviving pairs in the compact neighborhood. -/
theorem exists_finite_separation (T : X ≃ₜ X) {K : Set X} (hK : IsCompact K) (c : ℝ)
    (hexp : ∀ x ∈ isolatedCore T K, ∀ y ∈ isolatedCore T K,
      (∀ j : ℕ, dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
        dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ x y, (x, y) ∈ window T K c N → dist x y < ε := by
  have hcompact : IsCompact (window T K c 0) :=
    (hK.prod hK).of_isClosed_subset (window_closed T hK.isClosed c 0) (by
      intro z hz
      exact ⟨(hz 0 (by omega)).1, (hz 0 (by omega)).2.1⟩)
  have hcore : (⋂ n, window T K c n) ⊆ {z : X × X | dist z.1 z.2 < ε} := by
    intro z hz
    have hzn : ∀ j, z ∈ window T K c j := mem_iInter.mp hz
    have hx : z.1 ∈ isolatedCore T K :=
      ⟨fun j => (hzn j j le_rfl).1, fun j => (hzn j j le_rfl).2.2.2.1⟩
    have hy : z.2 ∈ isolatedCore T K :=
      ⟨fun j => (hzn j j le_rfl).2.1, fun j => (hzn j j le_rfl).2.2.2.2.1⟩
    have heq := hexp z.1 hx z.2 hy (fun j =>
      ⟨(hzn j j le_rfl).2.2.1, (hzn j j le_rfl).2.2.2.2.2⟩)
    change dist z.1 z.2 < ε
    simpa only [heq, dist_self] using hε
  obtain ⟨N, hN, hsubset⟩ := exists_pos_tail_subset_open hcompact
    (window_closed T hK.isClosed c) (window_antitone T K c)
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const) hcore
  exact ⟨N, hN, fun x y hxy => hsubset hxy⟩

/-- Literal forward/backward finite chart itineraries, restricted to the
compact surviving region at every observed time. -/
def itinerary {J : Type*} (T : X ≃ₜ X) (K : Set X) (charts : J → Set X)
    {N : ℕ} (forward backward : Fin (N + 1) → J) : Set X :=
  {x | ∀ j : Fin (N + 1),
    (T : X → X)^[j.val] x ∈ K ∩ charts (forward j) ∧
    (T.symm : X → X)^[j.val] x ∈ K ∩ charts (backward j)}

/-- An atlas of mesh below a core expansivity threshold is generating
on the actual two-sided finite survivor sets. -/
theorem exists_small_itineraries {J : Type*} (T : X ≃ₜ X) {K : Set X}
    (hK : IsCompact K) (c : ℝ) (charts : J → Set X)
    (hmesh : ∀ i, ∀ x ∈ charts i, ∀ y ∈ charts i, dist x y ≤ c)
    (hexp : ∀ x ∈ isolatedCore T K, ∀ y ∈ isolatedCore T K,
      (∀ j : ℕ, dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
        dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ forward backward : Fin (N + 1) → J,
      ∀ x ∈ itinerary T K charts forward backward,
      ∀ y ∈ itinerary T K charts forward backward, dist x y < ε := by
  obtain ⟨N, hN, hsep⟩ := exists_finite_separation T hK c hexp ε hε
  refine ⟨N, hN, ?_⟩
  intro forward backward x hx y hy
  apply hsep x y
  intro j hj
  let k : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hxj := hx k
  have hyj := hy k
  exact ⟨hxj.1.1, hyj.1.1, hmesh _ _ hxj.1.2 _ hyj.1.2,
    hxj.2.1, hyj.2.1, hmesh _ _ hxj.2.2 _ hyj.2.2⟩

end LeanShared.FiniteExpansiveCylinders
