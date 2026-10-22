module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordDistance
public import LeanShared.Dynamics.PseudoOrbitReferenceSelection

/-! Actual noisy backward block orbits near the hyperbolic core admit core
reference sequences with arbitrarily small deterministic pseudo-orbit error.
The spatial and noise tolerances precede all controls, paths and laws. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set LeanShared.FiniteJetComposition
open scoped NNReal

theorem Maps.exists_block_reference_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (N : ℕ) (error cap : ℝ) (positiveError : 0 < error) (positiveCap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ cap ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ Λ : Set M,
      ∀ controls : ℕ → ℕ → cube (ι := ι) ε, ∀ b : ℕ → M,
      (∀ n, b n ∈ Metric.thickening δ Λ) →
      (∀ n, word (fun j => F.family ε (controls n j).val) N (b (n + 1)) = b n) →
      ∃ reference : ℕ → Λ, (∀ n, dist (reference n).val (b n) < δ) ∧
        ∀ n, dist ((T : M → M)^[N] (reference (n + 1)).val) (reference n).val < error := by
  obtain ⟨δ, positiveδ, smallδ, select⟩ :=
    LeanShared.PseudoOrbitReferenceSelection.exists_reference_radius
      ((T : M → M)^[N])
      (CompactSpace.uniformContinuous_of_continuous (T.continuous.iterate N))
      error cap positiveError positiveCap
  obtain ⟨η, positiveη, close⟩ := F.exists_uniform_word_distance N (error / 3) (by positivity)
  refine ⟨δ, positiveδ, smallδ, η, positiveη, fun ε hp hw Λ controls b near step => ?_⟩
  apply select Λ b near
  intro n
  have estimate := close ε hp hw (controls n) (b (n + 1))
  rw [step n] at estimate
  simpa only [dist_comm] using estimate

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
