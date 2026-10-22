module

public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiverani1999

/-! Shrinking KL windows preserves every projector and convergence conclusion. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

def ProjectorOutputs.restrictWindow (o : ProjectorOutputs P i d q δ)
    (η : ℝ≥0) (hη : 0 < η) : ProjectorOutputs P i d q δ := {
  o with
  window := min o.window η
  window_pos := lt_min o.window_pos hη
  eigenvalue_near := fun ε hε => o.eigenvalue_near ε (hε.trans (min_le_left _ _))
  rank_one := fun ε hε => o.rank_one ε (hε.trans (min_le_left _ _))
  normalization := fun ε hε => o.normalization ε (hε.trans (min_le_left _ _))
  eigen_action := fun ε hε => o.eigen_action ε (hε.trans (min_le_left _ _))
  projection_commutes := fun ε hε => o.projection_commutes ε (hε.trans (min_le_left _ _))
  project_eigenvector := fun ε hε => o.project_eigenvector ε (hε.trans (min_le_left _ _))
  spectral_confinement := fun ε hε => o.spectral_confinement ε (hε.trans (min_le_left _ _))
  remainder_spectrum := fun ε hε => o.remainder_spectrum ε (hε.trans (min_le_left _ _))
  range_coercivity := fun ε hε => o.range_coercivity ε (hε.trans (min_le_left _ _)) }

/-- A neighborhood property at zero holds on a positive closed noise window.
The endpoint is retained so every subsequent restricted KL window can use ≤. -/
theorem exists_positive_window_of_eventually {p : ℝ≥0 → Prop}
    (hp : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), p ε) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε ≤ η, p ε := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hp
  let η : ℝ≥0 := ⟨r / 2, (half_pos hr).le⟩
  refine ⟨η, half_pos hr, ?_⟩
  intro ε hε
  apply hball
  rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
    abs_of_nonneg ε.coe_nonneg]
  exact (show (ε : ℝ) ≤ r / 2 from hε).trans_lt (half_lt_self hr)

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
