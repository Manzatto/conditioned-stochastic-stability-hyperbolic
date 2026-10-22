module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformChartWords
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseDifferentiableWords
public import LeanShared.Analysis.BoundedFramePerturbation
public import Mathlib.Tactic.FieldSimp

/-! Actual N-step noisy maps in arbitrary bounded centered frames. Both the
noise window and coordinate radius are uniform in the frames, controls and
compact centers. The derivative and forcing bounds are derived from literal
Whitney noise and genuine differentiability, not a supplied adapted cocycle. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates

theorem Maps.centered_word_window
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (C δ : ℝ) (positiveC : 0 < C) (positiveδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ a ∈ K, ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ C → ‖R.symm.toContinuousLinearMap‖ ≤ C →
      let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
      let g := d ∘ (T : M → M)^[N] ∘ c.symm
      ‖centered L R a (g a) f 0‖ ≤ δ / C ∧
      ∀ z : P, ‖z‖ ≤ radius →
        DifferentiableAt ℝ (centered L R a (g a) f) z ∧
        ‖fderiv ℝ (centered L R a (g a) f) z -
          fderiv ℝ (centered L R a (g a) g) z‖ ≤ δ := by
  have openDomain : IsOpen (c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source) :=
    ((T.continuous.iterate N).comp_continuousOn c.symm.continuousOn).isOpen_inter_preimage
      c.open_target d.open_source
  obtain ⟨ρ, positiveρ, tubeInside⟩ := compact.exists_cthickening_subset_open openDomain inside
  have tubeCompact := compact.cthickening (r := ρ)
  obtain ⟨ηb, positiveηb, bounds⟩ := F.uniform_chart_word_jets regularity deterministic
    c d hc hd N (Metric.cthickening ρ K) tubeCompact tubeInside
      (δ / (C * C)) (div_pos positiveδ (mul_pos positiveC positiveC))
  obtain ⟨ηd, positiveηd, differentiable⟩ := F.uniformly_differentiable_chart_words
    regularity deterministic c d hc hd N (Metric.cthickening ρ K) tubeCompact tubeInside
  refine ⟨ρ / C, div_pos positiveρ positiveC, min ηb ηd, lt_min positiveηb positiveηd,
    fun ε hp hw controls a ha L R boundL boundR => ?_⟩
  let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
  let g := d ∘ (T : M → M)^[N] ∘ c.symm
  have ballInside (z : P) (hz : ‖z‖ ≤ ρ / C) : a + L z ∈ Metric.cthickening ρ K := by
    apply Metric.mem_cthickening_of_dist_le _ a ρ K ha
    rw [dist_eq_norm, add_sub_cancel_left]
    calc
      ‖L z‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z‖ := L.toContinuousLinearMap.le_opNorm z
      _ ≤ C * (ρ / C) := mul_le_mul boundL hz (norm_nonneg z) positiveC.le
      _ = ρ := by field_simp
  have centerInside : a ∈ Metric.cthickening ρ K := Metric.self_subset_cthickening K ha
  have values : ‖f a - g a‖ ≤ δ / (C * C) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans
      (bounds ε hp (hw.trans (min_le_left _ _)) controls a centerInside)
  refine ⟨?_, fun z hz => ?_⟩
  · change ‖R.symm (f (a + L 0) - g a)‖ ≤ δ / C
    rw [_root_.map_zero, add_zero]
    calc
      ‖R.symm (f a - g a)‖ ≤ ‖R.symm.toContinuousLinearMap‖ * ‖f a - g a‖ :=
        R.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ C * (δ / (C * C)) := mul_le_mul boundR values (norm_nonneg _) positiveC.le
      _ = δ / C := by field_simp
  · have hi := ballInside z hz
    have df : DifferentiableAt ℝ f (a + L z) :=
      differentiable ε hp (hw.trans (min_le_right _ _)) controls _ hi
    have refPoint := tubeInside hi
    have dg : DifferentiableAt ℝ g (a + L z) := by
      have first : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 c.symm (a + L z) :=
        (contMDiffAt_symm_of_mem_maximalAtlas hc refPoint.1).of_le (by simp)
      have last : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 d
          ((T : M → M)^[N] (c.symm (a + L z))) :=
        (contMDiffAt_of_mem_maximalAtlas hd refPoint.2).of_le (by simp)
      exact (last.comp (a + L z) ((deterministic.iterate N).contMDiffAt.comp (a + L z) first)).contDiffAt.differentiableAt
        (by norm_num)
    refine ⟨R.symm.differentiableAt.comp z
      ((df.comp z (L.differentiableAt.const_add a)).sub_const (g a)), ?_⟩
    have derivativeBound : ‖fderiv ℝ f (a + L z) - fderiv ℝ g (a + L z)‖ ≤ δ / (C * C) :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans
        (bounds ε hp (hw.trans (min_le_left _ _)) controls _ hi)
    calc
      _ ≤ ‖R.symm.toContinuousLinearMap‖ * ((δ / (C * C)) * ‖L.toContinuousLinearMap‖) :=
        LeanShared.BoundedFramePerturbation.derivative_difference_le L R a (g a) f g z df dg _ derivativeBound
      _ ≤ C * ((δ / (C * C)) * C) := by gcongr
      _ = δ := by field_simp

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
