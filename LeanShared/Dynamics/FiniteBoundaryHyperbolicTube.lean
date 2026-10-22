module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicShooting

/-! A fixed endpoint ball gives a full-dimensional set of initial points
whose entire finite orbit stays in a uniform chart ball. The bound is
independent of the orbit length. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open scoped NNReal
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace U] [CompleteSpace S] {N : ℕ}

theorem orbit_coordinate_norm_le (d : Data U S N) (p : U × S) (j : Fin (N + 1)) :
    ‖d.orbit p j‖ ≤ ‖p‖ / (1 - (d.k + d.δ : ℝ≥0)) :=
  (norm_le_pi_norm _ j).trans (d.orbit_norm_le p)

theorem shooting_tube (d : Data U S N) (z : U × S) (r : ℝ)
    (small : ‖d.shooting z‖ < (1 - (d.k + d.δ : ℝ≥0)) * r)
    (j : ℕ) (hj : j ≤ N) : ‖d.evolve z j‖ < r := by
  have positive : 0 < 1 - ((d.k + d.δ : ℝ≥0) : ℝ) := sub_pos.mpr d.small
  have estimate := d.orbit_coordinate_norm_le (d.shooting z) (⟨j, by omega⟩ : Fin (N + 1))
  have same := d.evolve_orbit (d.shooting z) j hj
  rw [d.initial_shooting z] at same
  rw [← same] at estimate
  exact estimate.trans_lt ((div_lt_iff₀ positive).mpr (by simpa only [mul_comm] using small))

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
