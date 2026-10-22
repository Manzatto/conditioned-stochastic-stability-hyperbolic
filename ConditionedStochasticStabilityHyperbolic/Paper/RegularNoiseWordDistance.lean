module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseMovingWords
public import LeanShared.Dynamics.RobustFiniteIsolation
public import Mathlib.Tactic.FieldSimp

/-! A single noise window controls the actual N-step distance error over
ALL initial states and ALL time-varying controls on the compact manifold. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal
open LeanShared.FiniteJetComposition

theorem Maps.exists_uniform_word_distance
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (N : ℕ) (δ : ℝ) (positive : 0 < δ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ x : M,
      dist (word (fun n => F.family ε (controls n).val) N x) ((T : M → M)^[N] x) < δ := by
  obtain ⟨ξ, positiveξ, close⟩ := LeanShared.exists_uniform_finite_orbit_closeness
    (CompactSpace.uniformContinuous_of_continuous T.continuous) N positive
  let threshold : ℝ≥0 := ⟨ξ / (2 * F.constant),
    (div_pos positiveξ (mul_pos (by norm_num) F.constant_positive)).le⟩
  have positiveThreshold : 0 < threshold :=
    div_pos positiveξ (mul_pos (by norm_num) F.constant_positive)
  refine ⟨min F.window threshold, lt_min F.window_positive positiveThreshold,
    fun ε hp hw controls x => ?_⟩
  have scaleBound : (ε : ℝ) ≤ ξ / (2 * F.constant) := by
    exact_mod_cast hw.trans (min_le_right F.window threshold)
  have numeric : F.constant * (ε : ℝ) < ξ := calc
    _ ≤ F.constant * (ξ / (2 * F.constant)) :=
      mul_le_mul_of_nonneg_left scaleBound F.constant_positive.le
    _ = ξ / 2 := by field_simp [ne_of_gt F.constant_positive]
    _ < ξ := by linarith
  have result := close (fun n => word (fun j => F.family ε (controls j).val) n x)
    (fun n _ => (F.uniform_close ε hp (hw.trans (min_le_left F.window threshold))
      (controls n) (word (fun j => F.family ε (controls j).val) n x)).trans_lt numeric) N le_rfl
  exact result

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
