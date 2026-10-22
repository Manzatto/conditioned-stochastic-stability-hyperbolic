module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
import Mathlib.Tactic.Linarith

/-! The deterministic pressure gap selects all auxiliary contour parameters.
These numbers are constructed; they are not additional classical sources. -/

public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]

structure ContourParameters (P : S →L[ℂ] S) (d : DeterministicLeading P)
    (principal weak : ℝ) where
  cutoff : ℝ
  radius : ℝ
  principal_lt : principal < cutoff
  cutoff_lt_rate : cutoff < d.rate
  cutoff_lt_weak : cutoff < weak
  subordinate_lt : d.subordinate < cutoff
  cutoff_pos : 0 < cutoff
  radius_pos : 0 < radius
  radius_subordinate : radius < cutoff - d.subordinate
  radius_leading : radius < d.rate - cutoff

def contourParameters {P : S →L[ℂ] S} (d : DeterministicLeading P)
    (principal weak : ℝ) (hp : principal < d.rate) (hw : d.rate ≤ weak) :
    ContourParameters P d principal weak := by
  apply Classical.choice
  obtain ⟨q, hq, hqr⟩ := exists_between (max_lt hp d.subordinate_lt_rate)
  have hpq := (le_max_left principal d.subordinate).trans_lt hq
  have hsq := (le_max_right principal d.subordinate).trans_lt hq
  have hδ : 0 < min (q - d.subordinate) (d.rate - q) :=
    lt_min (sub_pos.mpr hsq) (sub_pos.mpr hqr)
  obtain ⟨δ, hδ0, hδmin⟩ := exists_between hδ
  exact ⟨{
    cutoff := q
    radius := δ
    principal_lt := hpq
    cutoff_lt_rate := hqr
    cutoff_lt_weak := hqr.trans_le hw
    subordinate_lt := hsq
    cutoff_pos := d.subordinate_nonneg.trans_lt hsq
    radius_pos := hδ0
    radius_subordinate := hδmin.trans_le (min_le_left _ _)
    radius_leading := hδmin.trans_le (min_le_right _ _) }⟩

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
