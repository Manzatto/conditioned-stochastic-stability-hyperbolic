module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniUniformResolvents
public import LeanShared.Analysis.WeakContourBound
public import LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.RieszContourIdempotent
import all LeanShared.Analysis.ContourProjectorContinuity

/-! Actual KL Riesz projectors converge in the original weak operator norm,
including an incomplete weak target. No projector stability contract is assumed. -/

public section
open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Weak convergence of actual Riesz contour projectors is derived from the
literal family hypotheses on any separated outer deterministic contour. -/
theorem Hypotheses.projector_convergence
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W} (h : Hypotheses P i)
    (q : ℝ) (hq : h.alpha < q) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (lower : ∀ z ∈ sphere c r, q ≤ ‖z‖)
    (res : sphere c r ⊆ resolventSet ℂ (P 0)) :
    Tendsto (fun ε => i.comp (LeanShared.RieszContourIdempotent.projector (P ε) c r -
      LeanShared.RieszContourIdempotent.projector (P 0) c r)) (𝓝 0) (𝓝 0) := by
  obtain ⟨_, _, actual, convergence⟩ := h.uniform_resolvent_convergence q hq
    (sphere c r) (isCompact_sphere c r) lower res
  have int0 : CircleIntegrable (resolvent (P 0)) c r :=
    (show ContinuousOn (resolvent (P 0)) (sphere c r) from fun z hz =>
      (spectrum.hasDerivAt_resolvent_const_left (res hz)).continuousAt.continuousWithinAt).circleIntegrable hr
  have ints : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), CircleIntegrable (resolvent (P ε)) c r := by
    filter_upwards [actual] with ε hε
    exact (show ContinuousOn (resolvent (P ε)) (sphere c r) from fun z hz =>
      (spectrum.hasDerivAt_resolvent_const_left (hε z hz).1).continuousAt.continuousWithinAt).circleIntegrable hr
  exact LeanShared.WeakContourBound.tendsto (compL ℂ E E W i)
    (fun ε => resolvent (P ε)) (resolvent (P 0)) c r hr int0 ints convergence

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
