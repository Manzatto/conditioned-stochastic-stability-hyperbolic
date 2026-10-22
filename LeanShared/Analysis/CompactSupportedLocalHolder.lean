module
public import LeanShared.Analysis.CompactLocalHolder
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Local fractional bounds on a compact support yield one global Hölder
constant in the ACTUAL proper metric. No global seminorm bound is assumed. -/
public noncomputable section
open Set Metric
open scoped BoundedContinuousFunction
namespace LeanShared.CompactSupportedLocalHolder
variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_bound (f : X →ᵇ ℂ) (compact : HasCompactSupport f)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (localBound : ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ W, ∀ z ∈ W,
        ‖f y - f z‖ ≤ C * dist y z ^ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖f x - f y‖ ≤ C * dist x y ^ a := by
  let K := cthickening 1 (tsupport f)
  have hK : IsCompact K := compact.cthickening
  obtain ⟨C, hC, bound⟩ := CompactLocalHolder.bound_on_compact ha ha1 hK (fun x => f x)
    (fun x _ => by simpa only [dist_eq_norm] using localBound x)
  refine ⟨max C (2 * ‖f‖), le_trans hC (le_max_left _ _), fun x y => ?_⟩
  by_cases small : dist x y ≤ 1
  · by_cases inside : x ∈ K ∧ y ∈ K
    · have h : ‖f x - f y‖ ≤ C * dist x y ^ a := by
        simpa only [dist_eq_norm] using bound x inside.1 y inside.2
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C (2 * ‖f‖))
        (Real.rpow_nonneg dist_nonneg _))
    · have zeros : f x = 0 ∧ f y = 0 := by
        have both {z w : X} (hzw : dist z w ≤ 1) (hz : f z ≠ 0) : z ∈ K ∧ w ∈ K := by
          have hs : z ∈ tsupport f := subset_tsupport f hz
          exact ⟨self_subset_cthickening (tsupport f) hs,
            mem_cthickening_of_dist_le w z 1 (tsupport f) hs (by simpa only [dist_comm] using hzw)⟩
        constructor
        · by_contra hx
          exact inside (both small hx)
        · by_contra hy
          have h := both (by simpa only [dist_comm] using small : dist y x ≤ 1) hy
          exact inside ⟨h.2, h.1⟩
      rw [zeros.1, zeros.2, sub_self, norm_zero]
      exact mul_nonneg (hC.trans (le_max_left _ _)) (Real.rpow_nonneg dist_nonneg _)
  · have far : 1 ≤ dist x y := (lt_of_not_ge small).le
    calc
      _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * ‖f‖ := by linarith [f.norm_coe_le_norm x, f.norm_coe_le_norm y]
      _ ≤ (2 * ‖f‖) * dist x y ^ a :=
        le_mul_of_one_le_right (by positivity) (Real.one_le_rpow far ha.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)
end LeanShared.CompactSupportedLocalHolder
