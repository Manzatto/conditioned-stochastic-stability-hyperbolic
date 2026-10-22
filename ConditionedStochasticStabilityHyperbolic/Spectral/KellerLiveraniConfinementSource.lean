module

public import LeanShared.Analysis.UniformTwoNormResolventStability
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinement
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniOuterResolvent
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProjectorWindowRestriction
import all ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniConfinement
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Primary Keller–Liverani spectral confinement proved from the actual
four-hypothesis family, using the quantitative weak-resolvent absorption
argument. No perturbative spectral source contract is assumed. -/

public section
open Filter Topology Set Metric
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The literal primary KL confinement contract is a theorem. -/
theorem classicalConfinementContract : ClassicalConfinementContract (E := E) (W := W) := by
  intro P i h q δ hq hqM hδ
  let M := h.weakRate
  have hM : 0 ≤ M := (h.alpha_pos.trans h.alpha_lt_weakRate).le
  let K := (closedBall (0 : ℂ) M ∩ {z : ℂ | q ≤ ‖z‖}) ∩
    {z : ℂ | ∀ w ∈ spectrum ℂ (P 0), δ ≤ dist z w}
  have closedSep : IsClosed {z : ℂ | ∀ w ∈ spectrum ℂ (P 0), δ ≤ dist z w} := by
    simp only [ofPred_forall]
    exact isClosed_iInter (fun w => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (continuous_id.dist continuous_const)))
  have compactK : IsCompact K :=
    ((isCompact_closedBall (0 : ℂ) M).inter_right
      (isClosed_le continuous_const continuous_norm)).inter_right closedSep
  have resK : K ⊆ resolventSet ℂ (P 0) := by
    intro z hz
    by_contra hn
    have contradiction := hz.2 z hn
    rw [dist_self] at contradiction
    exact (not_le_of_gt hδ) contradiction
  have continuousK : ContinuousOn (resolvent (P 0)) K := fun z hz =>
    (spectrum.hasDerivAt_resolvent_const_left (resK hz)).continuousAt.continuousWithinAt
  obtain ⟨L0, hL0⟩ := compactK.exists_bound_of_continuousOn continuousK
  let L := max L0 0
  have hL : 0 ≤ L := le_max_right _ _
  let bound := (h.strongConstant + h.errorConstant) * M
  have hbound : 0 ≤ bound := mul_nonneg
    (add_nonneg h.strongConstant_pos.le h.errorConstant_pos.le) hM
  obtain ⟨τ, normBound, hτ, _, stable⟩ := LeanShared.UniformTwoNormResolventStability.exists_bound
    (P 0) i h.alpha M h.strongConstant h.errorConstant h.weakConstant q M bound L
    h.alpha_pos.le hM h.strongConstant_pos.le h.errorConstant_pos.le h.weakConstant_pos.le
    hq hM hbound hL (h.twoNorm_growth 0 zero_le) (h.weak_growth 0 zero_le)
  let τnn : ℝ≥0 := ⟨τ, hτ.le⟩
  have small : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ h.window ∧ (h.modulus ε : ℝ) ≤ τ := by
    have original : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε < h.window := gt_mem_nhds h.window_pos
    have perturb := h.modulus_zero.eventually
      (gt_mem_nhds (show (0 : ℝ≥0) < τnn from hτ))
    filter_upwards [original, perturb] with ε hε hp
    exact ⟨hε.le, show (h.modulus ε : ℝ) ≤ τ from hp.le⟩
  obtain ⟨window, positive, hwindow⟩ := exists_positive_window_of_eventually small
  refine ⟨{ window := window, window_pos := positive, spectrum_near := ?_ }⟩
  intro ε hε z hspec
  by_cases hsmall : ‖z‖ ≤ q
  · exact Or.inl hsmall
  right
  by_contra! far
  have hεold := (hwindow ε hε).1
  have hzM : ‖z‖ ≤ M := h.norm_mem_spectrum_le_weakRate ε hεold z hspec
  have hzK : z ∈ K := ⟨⟨by simpa only [mem_closedBall, dist_zero_right] using hzM,
    (lt_of_not_ge hsmall).le⟩, fun w hw => (far w hw).le⟩
  have normP : ‖P ε‖ ≤ bound := by simpa only [pow_one] using h.power_norm_le ε hεold 1
  have perturb : ‖i.comp (P ε - P 0)‖ ≤ τ :=
    (h.perturbation ε hεold).trans (hwindow ε hε).2
  have actual := stable (P ε) normP (h.twoNorm_growth ε hεold) perturb z
    hzK.1.2 hzM (resK hzK) ((hL0 z hzK).trans (le_max_left _ _))
    (h.no_residual ε hεold z (hq.trans_le hzK.1.2))
  exact hspec actual.1

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
