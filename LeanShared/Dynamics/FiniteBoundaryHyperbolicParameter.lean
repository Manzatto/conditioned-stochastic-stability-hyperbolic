module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicUniqueness

/-! The actual two-boundary segment depends Lipschitz continuously on its
prescribed endpoints, with one bound independent of the orbit length. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform
open scoped NNReal
namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {N : ℕ}

theorem raw_parameter_distance (d : Data U S N) (p q : U × S)
    (z : Fin (N + 1) → U × S) : dist (d.raw p z) (d.raw q z) ≤ dist p q := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro j
  change max (dist _ _) (dist _ _) ≤ _
  apply max_le
  · by_cases before : j.val < N
    · simp only [raw, dite_eq_left before, dist_self]
      exact dist_nonneg
    · simpa only [raw, dite_eq_right before, Prod.dist_eq] using (le_max_left (dist p.1 q.1) (dist p.2 q.2))
  · by_cases after : 0 < j.val
    · simp only [raw, dite_eq_left after, dist_self]
      exact dist_nonneg
    · simpa only [raw, dite_eq_right after, Prod.dist_eq] using (le_max_right (dist p.1 q.1) (dist p.2 q.2))

variable [CompleteSpace U] [CompleteSpace S]

theorem orbit_parameter_distance (d : Data U S N) (p q : U × S) :
    dist (d.orbit p) (d.orbit q) ≤ dist p q / (1 - (d.k + d.δ : ℝ≥0)) := by
  have estimate := (d.transform_contracting p).dist_fixedPoint_le (d.orbit q)
  have fixedQ : d.raw q (d.orbit q) = d.orbit q :=
    (d.transform_contracting q).fixedPoint_isFixedPt
  calc
    _ = dist (d.orbit q) (d.orbit p) := dist_comm _ _
    _ ≤ dist (d.orbit q) (d.raw p (d.orbit q)) / (1 - (d.k + d.δ : ℝ≥0)) := estimate
    _ = dist (d.raw p (d.orbit q)) (d.raw q (d.orbit q)) / (1 - (d.k + d.δ : ℝ≥0)) := by
      rw [fixedQ, dist_comm]
    _ ≤ _ := div_le_div_of_nonneg_right (d.raw_parameter_distance p q (d.orbit q))
      (sub_pos.mpr (show ((d.k + d.δ : ℝ≥0) : ℝ) < 1 from d.small)).le

theorem orbit_norm_le (d : Data U S N) (boundary : U × S) :
    ‖d.orbit boundary‖ ≤ ‖boundary‖ / (1 - (d.k + d.δ : ℝ≥0)) := by
  have estimate := d.orbit_parameter_distance boundary 0
  simpa only [d.orbit_zero, dist_zero_right] using estimate

theorem orbit_continuous (d : Data U S N) : Continuous d.orbit := by
  apply continuous_iff_continuousAt.mpr
  intro q
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (fun p => d.orbit_parameter_distance p q)
  have limit := ((continuous_id.dist (continuous_const (y := q))).div_const
    (1 - ((d.k + d.δ : ℝ≥0) : ℝ))).continuousAt.tendsto (x := q)
  simpa only [id_eq, dist_self, zero_div] using limit

end Data
end LeanShared.FiniteBoundaryHyperbolicTransform
