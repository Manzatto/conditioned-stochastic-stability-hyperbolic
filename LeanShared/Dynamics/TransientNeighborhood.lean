module

public import LeanShared.Dynamics.RobustFiniteIsolation
import Mathlib.Tactic.Linarith

/-!
# The actual transient complement of a core neighborhood

If a compact region has its two-sided isolated core inside an open set `U`,
no trajectory can remain forever in `K \ U`. Thus every sufficiently small
sequence of perturbations uniformly enters `U` or exits `K` in finite time.
The assertions refer to the killed complement `K \ U`: subsequent returns
after entering `U` are not excluded, and the whole exterior is not declared
transient. No probability or function-space splitting is assumed here.
-/

@[expose] public section

open Set Function Metric

namespace LeanShared

variable {X : Type*}

section Topological

variable [TopologicalSpace X] [T2Space X]

/-- Every forward-trapped point in `K` eventually enters any open neighborhood
of its two-sided isolated core. Consequently its killed complement is empty. -/
theorem forwardTrapped_diff_eq_empty (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    forwardTrapped T (K \ U) = ∅ := by
  obtain ⟨N, _hN, htail⟩ := exists_pos_stable_tail_subset T hK hU hcore
  ext x
  constructor
  · intro hx
    have hbase : x ∈ forwardTrapped T K := fun n => (hx n).1
    have hNU : (T : X → X)^[N] x ∈ U := htail ⟨x, hbase, rfl⟩
    exact ((hx N).2 hNU).elim
  · intro hx
    exact hx.elim

/-- The deterministic finite horizon detects entrance into `U` or exit from
`K`, uniformly over the entire compact complement. -/
theorem exists_pos_uniform_entrance_or_exit (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K \ U, ∃ j ≤ N,
      (T : X → X)^[j] x ∉ K ∨ (T : X → X)^[j] x ∈ U := by
  have hL := hK.diff hU
  have hdis : Disjoint (K \ U) (forwardTrapped T (K \ U)) := by
    rw [forwardTrapped_diff_eq_empty T hK hU hcore]
    simp
  obtain ⟨N, hN, hexit⟩ :=
    exists_pos_uniform_forward_exit T.continuous hL.isClosed hL hdis
  refine ⟨N, hN, ?_⟩
  intro x hx
  obtain ⟨j, hj, hbad⟩ := hexit x hx
  exact ⟨j, hj, by simpa only [mem_sdiff, not_and_or, not_not] using hbad⟩

end Topological

section Metric

variable [MetricSpace X]

/-- The same entrance-or-exit horizon is robust for arbitrary finite
pseudo-orbits. One-step closeness is required only before leaving `K \ U`. -/
theorem exists_pos_robust_entrance_or_exit (T : X ≃ₜ X)
    (hT : UniformContinuous (T : X → X)) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℕ → X,
      z 0 ∈ K \ U →
      (∀ n < N, z n ∈ K \ U → dist (z (n + 1)) (T (z n)) < δ) →
      ∃ j ≤ N, z j ∉ K ∨ z j ∈ U := by
  have hL := hK.diff hU
  have hdis : Disjoint (K \ U) (forwardTrapped T (K \ U)) := by
    rw [forwardTrapped_diff_eq_empty T hK hU hcore]
    simp
  obtain ⟨N, hN, δ, hδ, hexit⟩ := exists_pos_robust_forward_exit hT hL.isClosed hL hdis
  refine ⟨N, hN, δ, hδ, ?_⟩
  intro z hz hstep
  obtain ⟨j, hj, hbad⟩ := hexit z hz hstep
  exact ⟨j, hj, by simpa only [mem_sdiff, not_and_or, not_not] using hbad⟩

/-- Arbitrary sequences of nearby maps have a common finite killed-complement
horizon. The maps need not be continuous or have a probability law. -/
theorem exists_pos_robust_entrance_or_exit_for_map_sequences (T : X ≃ₜ X)
    (hT : UniformContinuous (T : X → X)) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℕ → X → X,
      (∀ n < N, ∀ y ∈ K \ U, dist (F n y) (T y) < δ) →
      ∀ x ∈ K \ U, ∃ j ≤ N,
        nonautonomousOrbit F x j ∉ K ∨ nonautonomousOrbit F x j ∈ U := by
  obtain ⟨N, hN, δ, hδ, hexit⟩ := exists_pos_robust_entrance_or_exit T hT hK hU hcore
  refine ⟨N, hN, δ, hδ, ?_⟩
  intro F hF x hx
  exact hexit (nonautonomousOrbit F x) hx (fun n hn hy => hF n hn _ hy)

/-- On a compact metric ambient space the uniform-continuity input is automatic. -/
theorem exists_pos_robust_entrance_or_exit_of_compact [CompactSpace X]
    (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ F : ℕ → X → X,
      (∀ n < N, ∀ y ∈ K \ U, dist (F n y) (T y) < δ) →
      ∀ x ∈ K \ U, ∃ j ≤ N,
        nonautonomousOrbit F x j ∉ K ∨ nonautonomousOrbit F x j ∈ U :=
  exists_pos_robust_entrance_or_exit_for_map_sequences T
    (CompactSpace.uniformContinuous_of_continuous T.continuous) hK hU hcore

/-- The paper's uniform `C * epsilon` map-error hypothesis gives one common
noise threshold and entrance-or-exit horizon for every noise sequence. -/
theorem exists_small_noise_entrance_or_exit [CompactSpace X]
    (T : X ≃ₜ X) {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hcore : isolatedCore T K ⊆ U)
    (Ω : ℝ → Type*) (F : (ε : ℝ) → Ω ε → X → X)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise : ∀ ε > 0, ∀ ω : Ω ε, ∀ x ∈ K, dist (F ε ω x) (T x) ≤ C * ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ ω : ℕ → Ω ε, ∀ x ∈ K \ U, ∃ j ≤ N,
        nonautonomousOrbit (fun n => F ε (ω n)) x j ∉ K ∨
          nonautonomousOrbit (fun n => F ε (ω n)) x j ∈ U := by
  obtain ⟨N, hN, δ, hδ, hexit⟩ := exists_pos_robust_entrance_or_exit_of_compact T hK hU hcore
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨N, hN, δ / (C + 1), div_pos hδ hC1, ?_⟩
  intro ε hε hsmall ω x hx
  apply hexit (fun n => F ε (ω n)) _ x hx
  intro n _ y hy
  have hprod : ε * (C + 1) < δ := (lt_div_iff₀ hC1).mp hsmall
  have hbound := hnoise ε hε (ω n) y hy.1
  nlinarith

end Metric

end LeanShared
