module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseBackwardTail
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePseudoReferenceSelection
public import LeanShared.Dynamics.BackwardBlockSampling

/-! A surviving actual backward orbit has a uniformly chosen tail whose
block samples admit a core-valued pseudo-reference. Both horizons and the
noise threshold precede all controls and all surviving paths. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set LeanShared.FiniteJetComposition LeanShared.BackwardBlockUnrolling
open scoped NNReal

theorem Maps.exists_backward_tail_reference
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    {K Λ : Set M} (compact : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (N : ℕ) (error cap : ℝ) (positiveError : 0 < error) (positiveCap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ cap ∧ ∃ J : ℕ, 0 < J ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ b : ℕ → M,
      (∀ n, b n ∈ K) →
      (∀ n, F.family ε (controls n).val (b (n + 1)) = b n) →
      ∃ reference : ℕ → Λ,
        (∀ n, dist (reference n).val (b (J + N * n)) < δ) ∧
        ∀ n, dist ((T : M → M)^[N] (reference (n + 1)).val) (reference n).val < error := by
  obtain ⟨δ, positiveδ, smallδ, η₁, positiveη₁, select⟩ :=
    F.exists_block_reference_window N error cap positiveError positiveCap
  obtain ⟨J, positiveJ, η₂, positiveη₂, localize⟩ :=
    F.exists_uniform_backward_tail compact Metric.isOpen_thickening
      (core.trans (Metric.self_subset_thickening positiveδ Λ))
  refine ⟨δ, positiveδ, smallδ, J, positiveJ, min η₁ η₂,
    lt_min positiveη₁ positiveη₂, fun ε hp hw controls b inside step => ?_⟩
  let tail : ℕ → M := fun n => b (J + n)
  let f : ℕ → M → M := fun n => F.family ε (controls (J + n)).val
  have tailStep (n : ℕ) : f n (tail (n + 1)) = tail n := by
    simpa only [f, tail, Nat.add_assoc] using step (J + n)
  apply select ε hp (hw.trans (min_le_left _ _)) Λ
    (fun n j => controls (J + (N * (n + 1) - 1 - j))) (fun n => tail (N * n))
  · intro n
    exact localize ε hp (hw.trans (min_le_right _ _)) controls b inside step
      (J + N * n) (Nat.le_add_right _ _)
  · intro n
    exact LeanShared.BackwardBlockSampling.sampled_step f tail tailStep N n

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
