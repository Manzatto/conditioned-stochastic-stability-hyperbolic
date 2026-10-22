module

public import LeanShared.Dynamics.HyperbolicShadowing
public import LeanShared.Dynamics.FiniteWindowContraction
import Mathlib.Tactic.Ring

/-! Actual split nonlinear hyperbolic trajectories become exponentially
close away from the endpoints of any finite window. No exponential
matching or Bowen bound is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicShadowing.Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem raw_eq_of_adjacent (d : Data U S) (z : ℤ → U × S) (j : ℤ)
    (previousStep : d.map (j - 1) (z j) = z (j - 1))
    (currentStep : d.map j (z (j + 1)) = z j) : d.raw z j = z j := by
  have previous := congrArg Prod.fst previousStep
  have current := congrArg Prod.snd currentStep
  simp only [map] at previous current
  apply Prod.ext
  · change (d.expanding (j - 1)).symm _ = _
    apply (d.expanding (j - 1)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (eq_sub_of_add_eq previous).symm
  · exact current

theorem raw_eq_of_steps (d : Data U S) (z : ℤ → U × S)
    (step : ∀ j, d.map j (z (j + 1)) = z j) (j : ℤ) : d.raw z j = z j := by
  have previous := congrArg Prod.fst (step (j - 1))
  have current := congrArg Prod.snd (step j)
  simp only [map, sub_add_cancel] at previous
  simp only [map] at current
  apply Prod.ext
  · change (d.expanding (j - 1)).symm _ = _
    apply (d.expanding (j - 1)).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (eq_sub_of_add_eq previous).symm
  · exact current

theorem raw_distance_local (d : Data U S) (z w : ℤ → U × S) (j : ℤ) :
    dist (d.raw z j) (d.raw w j) ≤ ((d.k : ℝ) + d.δ) *
      max (dist (z (j - 1)) (w (j - 1)))
        (max (dist (z j) (w j)) (dist (z (j + 1)) (w (j + 1)))) := by
  let D := max (dist (z (j - 1)) (w (j - 1)))
    (max (dist (z j) (w j)) (dist (z (j + 1)) (w (j + 1))))
  let v (m : ℤ) := if m = j - 1 ∨ m = j ∨ m = j + 1 then z m else w m
  have nonnegative : 0 ≤ D := dist_nonneg.trans (le_max_left _ _)
  have bounded (m : ℤ) : dist (v m) (w m) ≤ D := by
    dsimp [v]
    split_ifs with hm
    · rcases hm with hm | hm | hm
      · subst m; exact le_max_left _ _
      · subst m; exact (le_max_left _ _).trans (le_max_right _ _)
      · subst m; exact (le_max_right _ _).trans (le_max_right _ _)
    · simpa only [dist_self] using nonnegative
  have equal : d.raw v j = d.raw z j := by simp [raw, v]
  have estimate := d.raw_distance v w D bounded j
  rw [equal] at estimate
  exact estimate

theorem finite_window_steps (d : Data U S) (z w : ℤ → U × S)
    (M : ℝ) (n : ℕ)
    (zstep : ∀ j : ℕ, j < n → d.map j (z (j + 1)) = z j)
    (wstep : ∀ j : ℕ, j < n → d.map j (w (j + 1)) = w j)
    (bounded : ∀ j : ℕ, j ≤ n → dist (z j) (w j) ≤ M) :
    ∀ j : ℕ, j ≤ n → dist (z j) (w j) ≤
      ((d.k : ℝ) + d.δ) ^ min j (n - j) * M := by
  apply FiniteWindowContraction.bound (fun j : ℕ => dist (z j) (w j))
    ((d.k : ℝ) + d.δ) M (add_nonneg d.k.coe_nonneg d.δ.coe_nonneg) n bounded
  intro j positive hj
  have previous : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  have zp : d.map ((j : ℤ) - 1) (z j) = z ((j : ℤ) - 1) := by
    have step := zstep (j - 1) (by omega)
    simpa only [previous, Nat.sub_add_cancel positive, sub_add_cancel] using step
  have wp : d.map ((j : ℤ) - 1) (w j) = w ((j : ℤ) - 1) := by
    have step := wstep (j - 1) (by omega)
    simpa only [previous, Nat.sub_add_cancel positive, sub_add_cancel] using step
  have estimate := d.raw_distance_local z w (j : ℤ)
  rw [d.raw_eq_of_adjacent z _ zp (zstep j hj),
    d.raw_eq_of_adjacent w _ wp (wstep j hj)] at estimate
  simpa only [previous, Nat.cast_add, Nat.cast_one] using estimate

theorem finite_window_distance (d : Data U S) (z w : ℤ → U × S)
    (zstep : ∀ j, d.map j (z (j + 1)) = z j)
    (wstep : ∀ j, d.map j (w (j + 1)) = w j)
    (M : ℝ) (n : ℕ) (bounded : ∀ j : ℕ, j ≤ n → dist (z j) (w j) ≤ M) :
    ∀ j : ℕ, j ≤ n → dist (z j) (w j) ≤
      ((d.k : ℝ) + d.δ) ^ min j (n - j) * M := by
  apply FiniteWindowContraction.bound (fun j : ℕ => dist (z j) (w j))
    ((d.k : ℝ) + d.δ) M (add_nonneg d.k.coe_nonneg d.δ.coe_nonneg) n bounded
  intro j positive _
  have estimate := d.raw_distance_local z w (j : ℤ)
  rw [d.raw_eq_of_steps z zstep, d.raw_eq_of_steps w wstep] at estimate
  have previous : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  simpa only [previous, Nat.cast_add, Nat.cast_one] using estimate

end LeanShared.HyperbolicShadowing.Data
