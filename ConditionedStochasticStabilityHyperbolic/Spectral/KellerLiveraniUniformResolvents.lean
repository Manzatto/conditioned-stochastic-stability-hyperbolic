module

public import LeanShared.Analysis.UniformTwoNormResolventConvergence
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniOuterResolvent
import Mathlib.Tactic.Positivity

/-! Literal KL hypotheses give uniform actual resolvents and uniform weak
resolvent convergence on compact deterministic resolvent sets. -/

public section
open Filter Topology Set
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The actual family has uniformly bounded resolvents and uniform weak
resolvent convergence on compact sets outside the strong disk and away from
the deterministic spectrum. No classical KL contract is an argument. -/
theorem Hypotheses.uniform_resolvent_convergence
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W} (h : Hypotheses P i)
    (q : ℝ) (hq : h.alpha < q) (K : Set ℂ) (hK : IsCompact K)
    (lower : ∀ z ∈ K, q ≤ ‖z‖) (res : K ⊆ resolventSet ℂ (P 0)) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ᶠ ε in 𝓝 (0 : ℝ≥0), ∀ z ∈ K,
        z ∈ resolventSet ℂ (P ε) ∧ ‖resolvent (P ε) z‖ ≤ L) ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ∀ z ∈ K,
        ‖i.comp (resolvent (P ε) z - resolvent (P 0) z)‖ ≤ δ := by
  obtain ⟨outer0, houter0⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  let outer := max outer0 0
  have continuousK : ContinuousOn (resolvent (P 0)) K := fun z hz =>
    (spectrum.hasDerivAt_resolvent_const_left (res hz)).continuousAt.continuousWithinAt
  obtain ⟨L0, hL0⟩ := hK.exists_bound_of_continuousOn continuousK
  let L := max L0 0
  have hM : 0 ≤ h.weakRate := (h.alpha_pos.trans h.alpha_lt_weakRate).le
  let bound := (h.strongConstant + h.errorConstant) * h.weakRate
  have hbound : 0 ≤ bound := mul_nonneg
    (add_nonneg h.strongConstant_pos.le h.errorConstant_pos.le) hM
  have window : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ h.window :=
    (gt_mem_nhds h.window_pos).mono (fun _ hh => hh.le)
  have good : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ‖P ε‖ ≤ bound ∧
      (∀ n x, ‖(P ε ^ n) x‖ ≤ h.strongConstant * h.alpha ^ n * ‖x‖ +
        h.errorConstant * h.weakRate ^ n * ‖i x‖) ∧
      ∀ z ∈ K, Function.Injective (z • (1 : E →L[ℂ] E) - P ε) →
        DenseRange (z • (1 : E →L[ℂ] E) - P ε) := by
    filter_upwards [window] with ε hε
    refine ⟨?_, h.twoNorm_growth ε hε, fun z hz => h.no_residual ε hε z (hq.trans_le (lower z hz))⟩
    simpa only [pow_one] using h.power_norm_le ε hε 1
  have modulusReal : Tendsto (fun ε => (h.modulus ε : ℝ)) (𝓝 (0 : ℝ≥0)) (𝓝 0) := by
    exact (NNReal.continuous_coe.tendsto (0 : ℝ≥0)).comp h.modulus_zero
  have perturbation : Tendsto (fun ε => ‖i.comp (P ε - P 0)‖) (𝓝 (0 : ℝ≥0)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
      (window.mono (fun ε hε => h.perturbation ε hε)) modulusReal
  exact LeanShared.UniformTwoNormResolventConvergence.exists_bound_and_convergence P (P 0) i
    (𝓝 (0 : ℝ≥0)) K h.alpha h.weakRate h.strongConstant h.errorConstant h.weakConstant
    q outer bound L h.alpha_pos.le hM h.strongConstant_pos.le h.errorConstant_pos.le
    h.weakConstant_pos.le hq (le_max_right _ _) hbound (le_max_right _ _)
    (h.twoNorm_growth 0 zero_le) (h.weak_growth 0 zero_le)
    (fun z hz => ⟨lower z hz, (houter0 z hz).trans (le_max_left _ _), res hz,
      (hL0 z hz).trans (le_max_left _ _)⟩) good perturbation

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
