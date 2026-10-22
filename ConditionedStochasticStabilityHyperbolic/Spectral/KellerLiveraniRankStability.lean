module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniProjectorProfile
public import LeanShared.Analysis.WeakProjectorRankStability

/-! Normalized rank-one factorization of the actual noisy Riesz projector,
derived from the literal KL hypotheses. No rank-stability source is assumed. -/

public section
open Filter Topology Set Metric ContinuousLinearMap
open scoped NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem Hypotheses.rank_profile
    {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W} (h : Hypotheses P i)
    (q : ℝ) (hq : h.alpha < q) (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (excludes : (0 : ℂ) ∉ closedBall c r)
    (lower : ∀ z ∈ closedBall c R \ ball c r, q ≤ ‖z‖)
    (res : closedBall c R \ ball c r ⊆ resolventSet ℂ (P 0))
    (ℓ₀ : E →L[ℂ] ℂ) (v : E) (normalization : ℓ₀ v = 1)
    (zero : LeanShared.RieszContourIdempotent.projector (P 0) c r = ℓ₀.smulRight v) :
    ∃ C : ℝ, 0 ≤ C ∧
      Tendsto (fun ε => i.comp (LeanShared.RieszContourIdempotent.projector (P ε) c r -
        ℓ₀.smulRight v)) (𝓝 0) (𝓝 0) ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ≥0),
        sphere c r ⊆ resolventSet ℂ (P ε) ∧
        LeanShared.RieszContourIdempotent.projector (P ε) c r *
          LeanShared.RieszContourIdempotent.projector (P ε) c r =
          LeanShared.RieszContourIdempotent.projector (P ε) c r ∧
        P ε * LeanShared.RieszContourIdempotent.projector (P ε) c r =
          LeanShared.RieszContourIdempotent.projector (P ε) c r * P ε ∧
        (∀ x : E, ‖(LeanShared.RieszContourIdempotent.projector (P ε) c r) x‖ ≤
          C * ‖i ((LeanShared.RieszContourIdempotent.projector (P ε) c r) x)‖) ∧
        ∃ ℓ : E →L[ℂ] ℂ,
          ℓ ((LeanShared.RieszContourIdempotent.projector (P ε) c r) v) = 1 ∧
          LeanShared.RieszContourIdempotent.projector (P ε) c r =
            ℓ.smulRight ((LeanShared.RieszContourIdempotent.projector (P ε) c r) v) := by
  have circle : sphere c r ⊆ closedBall c R \ ball c r := by
    intro z hz
    exact ⟨(sphere_subset_closedBall hz).trans hrR.le, fun hb => (ne_of_lt hb) hz⟩
  have convergence := h.projector_convergence q hq c r hr.le
    (fun z hz => lower z (circle hz)) (fun z hz => res (circle hz))
  rw [zero] at convergence
  obtain ⟨C, hC, profile⟩ := h.projector_profile q hq c r R hr hrR excludes lower res
  have projections : ∀ᶠ ε in 𝓝 (0 : ℝ≥0),
      LeanShared.RieszContourIdempotent.projector (P ε) c r *
          LeanShared.RieszContourIdempotent.projector (P ε) c r =
          LeanShared.RieszContourIdempotent.projector (P ε) c r ∧
      ∀ x : E, ‖(LeanShared.RieszContourIdempotent.projector (P ε) c r) x‖ ≤
        C * ‖i ((LeanShared.RieszContourIdempotent.projector (P ε) c r) x)‖ := by
    filter_upwards [profile] with ε hε
    exact ⟨by simpa only [pow_two] using hε.2.1, hε.2.2.2⟩
  have rank := LeanShared.WeakProjectorRankStability.eventually_factorization
    (fun ε => LeanShared.RieszContourIdempotent.projector (P ε) c r) i h.weak_injective
    ℓ₀ v normalization C hC convergence projections
  refine ⟨C, hC, convergence, ?_⟩
  filter_upwards [profile, projections, rank] with ε hp hproj hrank
  exact ⟨hp.1, hproj.1, hp.2.2.1, hproj.2, hrank⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
