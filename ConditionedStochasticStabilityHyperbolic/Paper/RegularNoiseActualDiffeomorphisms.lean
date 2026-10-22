module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseActualHomeomorphisms
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseGlobalDifferential
public import LeanShared.Geometry.HomeomorphismInverseRegularity

/-! Actual small perturbations are C1 diffeomorphisms. Both inverse state
regularity and joint inverse continuity are derived from the literal Whitney
noise, rather than provided in an inverse-calculus packet. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 2400000 in
theorem Maps.exists_actual_diffeomorphisms
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ F.window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∃ H : cube (ι := ι) ε → M ≃ₜ M,
        (∀ a x, H a x = F.family ε a.val x) ∧
        (∀ a, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H a) ∧
          ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H a).symm) ∧
        Continuous (fun p : cube (ι := ι) ε × M => (H p.1).symm p.2) := by
  obtain ⟨ηh,positiveηh,ηhWindow,homeos⟩ := F.exists_actual_homeomorphisms regularity deterministic inverse
  obtain ⟨ηd,positiveηd,differentials⟩ := F.exists_global_differential_window regularity deterministic inverse
  refine ⟨min ηh ηd,lt_min positiveηh positiveηd,(min_le_left _ _).trans ηhWindow,
    fun ε hp hw => ?_⟩
  obtain ⟨H,identity,continuous⟩ := homeos ε hp (hw.trans (min_le_left _ _))
  refine ⟨H,identity,fun a => ?_,continuous⟩
  have actual : (H a : M → M) = F.family ε a.val := funext (identity a)
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (H a) := by
    rw [actual]
    apply (F.map_regular ε hp ((hw.trans (min_le_left _ _)).trans ηhWindow) a).differentiable.of_le
    exact_mod_cast (Nat.le_floor (by simpa using regularity) : (1 : ℕ) ≤ ⌊r⌋₊)
  refine ⟨forward,fun y => ?_⟩
  have bijective : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (H a) ((H a).symm y)) := by
    rw [actual]
    exact differentials ε hp (hw.trans (min_le_right _ _)) a _
  simpa only [Homeomorph.apply_symm_apply] using
    LeanShared.HomeomorphismInverseRegularity.contMDiffAt_symm (H a) ((H a).symm y)
      (forward.contMDiffAt) bijective

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
