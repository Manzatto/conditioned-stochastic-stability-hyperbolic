module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseCloseness
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Original inverse maps converge uniformly with their genuine continuity
modulus; all controls and all states share one window. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal

theorem Maps.inverse_uniform_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (error : ℝ) (positive : 0 < error) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ a : cube (ι := ι) ε, ∀ J : M → M,
      Function.RightInverse J (F.family ε a.val) → ∀ y, dist (J y) (T.symm y) < error := by
  obtain ⟨δ,positiveδ,close⟩ := LeanShared.UniformInverseCloseness.exists_radius T
    (CompactSpace.uniformContinuous_of_continuous T.symm.continuous) error positive
  let threshold : ℝ≥0 := ⟨δ / (2 * F.constant),
    (div_pos positiveδ (mul_pos (by norm_num) F.constant_positive)).le⟩
  have positiveThreshold : 0 < threshold := div_pos positiveδ (mul_pos (by norm_num) F.constant_positive)
  refine ⟨min F.window threshold,lt_min F.window_positive positiveThreshold,min_le_left _ _,
    fun ε hp hw a J right => close (F.family ε a.val) J ?_ right⟩
  intro x
  have scale : (ε : ℝ) ≤ δ / (2 * F.constant) := by
    exact_mod_cast hw.trans (min_le_right _ _)
  have small : F.constant * (ε : ℝ) < δ := calc
    _ ≤ F.constant * (δ / (2 * F.constant)) := mul_le_mul_of_nonneg_left scale F.constant_positive.le
    _ = δ / 2 := by field_simp [ne_of_gt F.constant_positive]
    _ < δ := half_lt_self positiveδ
  exact (F.uniform_close ε hp (hw.trans (min_le_left _ _)) a x).trans_lt small

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
