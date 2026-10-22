module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Dynamics.BackwardTailLocalization
public import Mathlib.Tactic.FieldSimp

/-! Every actual noisy backward orbit staying in an isolating compact set
has a uniformly localized tail. The horizon and noise threshold precede all
controls and orbits, and are independent of every driving law. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal

theorem Maps.exists_uniform_backward_tail
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    {K U : Set M} (compact : IsCompact K) (openU : IsOpen U)
    (core : LeanShared.isolatedCore T K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ b : ℕ → M,
      (∀ n, b n ∈ K) →
      (∀ n, F.family ε (controls n).val (b (n + 1)) = b n) →
      ∀ n, N ≤ n → b n ∈ U := by
  obtain ⟨N, positiveN, δ, positiveδ, localize⟩ :=
    LeanShared.exists_uniform_backward_tail_localization T (CompactSpace.uniformContinuous_of_continuous T.continuous)
      (CompactSpace.uniformContinuous_of_continuous T.symm.continuous) compact openU core
  let threshold : ℝ≥0 := ⟨δ / (2 * F.constant), (div_pos positiveδ (mul_pos (by norm_num) F.constant_positive)).le⟩
  have thresholdPositive : 0 < threshold := by
    exact div_pos positiveδ (mul_pos (by norm_num) F.constant_positive)
  refine ⟨N, positiveN, min F.window threshold,
    lt_min F.window_positive thresholdPositive, fun ε hp hw controls b inside step => ?_⟩
  apply localize b inside
  intro n
  rw [← step n]
  have scaleBound : (ε : ℝ) ≤ δ / (2 * F.constant) := by
    exact_mod_cast hw.trans (min_le_right F.window threshold)
  have numeric : F.constant * (ε : ℝ) < δ := calc
    _ ≤ F.constant * (δ / (2 * F.constant)) :=
      mul_le_mul_of_nonneg_left scaleBound F.constant_positive.le
    _ = δ / 2 := by field_simp [ne_of_gt F.constant_positive]
    _ < δ := by linarith
  exact (F.uniform_close ε hp (hw.trans (min_le_left F.window threshold))
    (controls n) (b (n + 1))).trans_lt numeric

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
