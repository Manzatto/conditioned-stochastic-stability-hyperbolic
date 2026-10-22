module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniProjectorConvergence
public import LeanShared.Analysis.UniformRieszRangeCoercivity
public import LeanShared.Analysis.RieszInverseMoment
public import LeanShared.Analysis.RieszContourEigenvectors
import all LeanShared.Analysis.RieszInverseMoment
import Mathlib.Tactic.Linarith

/-! Actual KL Riesz projectors have uniform range coercivity, idempotence and
commutation, derived from the original hypotheses and separated contours. -/

public section
open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A separated deterministic annulus generates actual noisy Riesz projectors
with uniform range coercivity. No rank or coercivity premise is supplied. -/
theorem Hypotheses.projector_profile
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W} (h : Hypotheses P i)
    (q : ℝ) (hq : h.alpha < q) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (excludes : (0 : ℂ) ∉ closedBall c r)
    (lower : ∀ z ∈ closedBall c R \ ball c r, q ≤ ‖z‖)
    (res : closedBall c R \ ball c r ⊆ resolventSet ℂ (P 0)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ ε in 𝓝 (0 : ℝ≥0),
      sphere c r ⊆ resolventSet ℂ (P ε) ∧
      (LeanShared.RieszContourIdempotent.projector (P ε) c r) ^ 2 =
        LeanShared.RieszContourIdempotent.projector (P ε) c r ∧
      P ε * LeanShared.RieszContourIdempotent.projector (P ε) c r =
        LeanShared.RieszContourIdempotent.projector (P ε) c r * P ε ∧
      ∀ x : E, ‖(LeanShared.RieszContourIdempotent.projector (P ε) c r) x‖ ≤
        K * ‖i ((LeanShared.RieszContourIdempotent.projector (P ε) c r) x)‖ := by
  have compact : IsCompact (closedBall c R \ ball c r) :=
    (isCompact_closedBall c R).inter_right isOpen_ball.isClosed_compl
  obtain ⟨L, hL, actual, _⟩ := h.uniform_resolvent_convergence q hq
    (closedBall c R \ ball c r) compact lower res
  have circle : sphere c r ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨(sphere_subset_closedBall hz).trans hrR.le, fun hb => (ne_of_lt hb) hz⟩
  let outer := ‖c‖ + r
  have houter : 0 ≤ outer := add_nonneg (norm_nonneg c) hr.le
  have upper : ∀ z ∈ sphere c r, ‖z‖ ≤ outer := by
    intro z hz
    have hh : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (z - c) c
    rw [← dist_eq_norm, mem_sphere.mp hz] at hh
    exact hh.trans_eq (add_comm _ _)
  obtain ⟨K, hK, coercive⟩ := LeanShared.UniformRieszRangeCoercivity.exists_bound i
    h.alpha h.weakRate h.strongConstant h.errorConstant h.weakConstant q outer L c r
    h.alpha_pos.le (h.alpha_pos.trans h.alpha_lt_weakRate).le h.strongConstant_pos.le
    h.errorConstant_pos.le h.weakConstant_pos.le hq houter hL hr.le
    (fun z hz => lower z (circle hz)) upper
  have oldWindow : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε ≤ h.window :=
    (gt_mem_nhds h.window_pos).mono (fun _ hh => hh.le)
  refine ⟨K, hK, ?_⟩
  filter_upwards [actual, oldWindow] with ε hactual hε
  have resε : sphere c r ⊆ resolventSet ℂ (P ε) := fun z hz => (hactual z (circle hz)).1
  have idempotent := LeanShared.RieszContourIdempotent.idempotent (P ε) c r R hr hrR
    (fun z hz => (hactual z hz).1)
  have idem : (LeanShared.RieszContourIdempotent.projector (P ε) c r) ^ 2 =
      LeanShared.RieszContourIdempotent.projector (P ε) c r := by simpa only [pow_two] using idempotent
  refine ⟨resε, idem, LeanShared.RieszContourIdempotent.projector_commutes (P ε) c r hr.le resε, ?_⟩
  exact coercive (P ε) (h.twoNorm_growth ε hε) (h.weak_growth ε hε) resε
    (fun z hz => (hactual z (circle hz)).2) idem
    (fun n => (LeanShared.RieszInverseMoment.powers (P ε) n c r hr.le excludes resε).1)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
