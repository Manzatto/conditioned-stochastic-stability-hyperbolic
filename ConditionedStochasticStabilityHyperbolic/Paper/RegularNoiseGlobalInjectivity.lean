module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseLocalInjectivity
public import LeanShared.Topology.UniformLocalInjectivityWindows
public import LeanShared.Topology.GlobalInjectivityNearHomeomorphism

/-! Literal small Whitney perturbations of a diffeomorphism on the compact
manifold are globally injective. Uniform local injectivity, compactness and
C0 closeness are proved inputs, not inverse-map source fields. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 2400000 in
theorem Maps.exists_global_injectivity_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ a : cube (ι := ι) ε,
      Function.Injective (F.family ε a.val) := by
  obtain ⟨radius,positiveRadius,localWindow,positiveLocalWindow,locally⟩ :=
    LeanShared.UniformLocalInjectivityWindows.exists_window (fun ε => ↥(cube (ι := ι) ε))
      (fun ε a => F.family ε a.val)
      (F.exists_local_injectivity_window regularity deterministic inverse)
  obtain ⟨δ,positiveδ,injective⟩ := LeanShared.GlobalInjectivityNearHomeomorphism.exists_radius T
    (CompactSpace.uniformContinuous_of_continuous T.symm.continuous) radius positiveRadius
  let threshold : ℝ≥0 := ⟨δ / (2 * F.constant),
    (div_pos positiveδ (mul_pos (by norm_num) F.constant_positive)).le⟩
  have positiveThreshold : 0 < threshold := div_pos positiveδ (mul_pos (by norm_num) F.constant_positive)
  refine ⟨min F.window (min localWindow threshold),lt_min F.window_positive
    (lt_min positiveLocalWindow positiveThreshold),fun ε hp hw a => ?_⟩
  apply injective (F.family ε a.val)
  · intro x
    have scale : (ε : ℝ) ≤ δ / (2 * F.constant) := by
      exact_mod_cast hw.trans ((min_le_right _ _).trans (min_le_right _ _))
    have small : F.constant * (ε : ℝ) < δ := calc
      _ ≤ F.constant * (δ / (2 * F.constant)) := mul_le_mul_of_nonneg_left scale F.constant_positive.le
      _ = δ / 2 := by field_simp [ne_of_gt F.constant_positive]
      _ < δ := half_lt_self positiveδ
    exact (F.uniform_close ε hp (hw.trans (min_le_left _ _)) a x).trans_lt small
  · exact locally ε hp (hw.trans ((min_le_right _ _).trans (min_le_left _ _))) a

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
