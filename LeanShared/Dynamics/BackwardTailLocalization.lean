module
public import LeanShared.Dynamics.RobustFiniteIsolation

/-! Every sufficiently small backward pseudo-orbit that stays in a compact
isolating set has its entire tail in any prescribed neighborhood of the
isolated core. This is uniform in the orbit and needs no hyperbolicity. -/
public noncomputable section
namespace LeanShared
open Set Metric

theorem exists_uniform_backward_tail_localization
    {X : Type*} [MetricSpace X] (T : X ≃ₜ X)
    (forward : UniformContinuous (T : X → X))
    (inverse : UniformContinuous (T.symm : X → X))
    {K U : Set X} (compact : IsCompact K) (openU : IsOpen U)
    (core : isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ η : ℝ, 0 < η ∧ ∀ b : ℕ → X,
      (∀ n, b n ∈ K) → (∀ n, dist (b n) (T (b (n + 1))) < η) →
      ∀ n, N ≤ n → b n ∈ U := by
  obtain ⟨N, positiveN, δ, positiveδ, localize⟩ :=
    exists_pos_robust_finite_isolation T forward inverse compact openU core
  obtain ⟨γ, positiveγ, inverseClose⟩ := Metric.uniformContinuous_iff.mp inverse δ positiveδ
  refine ⟨N, positiveN, min δ γ, lt_min positiveδ positiveγ, fun b inside small n hn => ?_⟩
  let a : ℕ → X := fun j => b (n - j)
  let c : ℕ → X := fun j => b (n + j)
  have middle : a 0 = c 0 := by simp only [a, c, Nat.sub_zero, Nat.add_zero]
  have future : ∀ j < N, dist (a (j + 1)) (T (a j)) < δ := by
    intro j hj
    have step := small (n - (j + 1))
    have index : n - (j + 1) + 1 = n - j := by omega
    simpa only [a, index] using step.trans_le (min_le_left δ γ)
  have past : ∀ j < N, dist (c (j + 1)) (T.symm (c j)) < δ := by
    intro j _
    have step := (small (n + j)).trans_le (min_le_right δ γ)
    have estimate := inverseClose step
    simpa only [c, T.symm_apply_apply, Nat.add_assoc, dist_comm] using estimate
  exact localize a c middle (fun _ _ => inside _) (fun _ _ => inside _) future past

end LeanShared
