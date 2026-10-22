module
public import LeanShared.Analysis.ParameterizedContraction
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Continuity of finite-coordinate observations of contraction fixed points.
The parameterized transformations need not be continuous in the uniform norm.
Only the observed finite iterates are required to be continuous, together with
one uniform displacement bound at the starting point. This accommodates the
product topology on entire noise paths. -/
public noncomputable section
namespace LeanShared.ParameterizedContraction
open Filter
open scoped Topology NNReal

theorem continuous_observation {P X Y : Type*} [TopologicalSpace P]
    [MetricSpace X] [CompleteSpace X] [Nonempty X] [MetricSpace Y]
    (T : P → X → X) (k : ℝ≥0) (small : k < 1) (contract : ∀ p, ContractingWith k (T p))
    (x : X) (M : ℝ) (displacement : ∀ p, dist x (T p x) ≤ M)
    (observe : X → Y) (nonexpansive : LipschitzWith 1 observe)
    (iterate_continuous : ∀ n : ℕ, Continuous (fun p => observe ((T p)^[n] x))) :
    Continuous (fun p => observe (point T k contract p)) := by
  have uniform : TendstoUniformly (fun n p => observe ((T p)^[n] x))
      (fun p => observe (point T k contract p)) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε positive
    have limit : Tendsto (fun n : ℕ => M * (k : ℝ)^n / (1 - k)) atTop (𝓝 0) := by
      simpa only [mul_zero, zero_div] using
        (tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one k.coe_nonneg small)).div_const
            (1 - (k : ℝ))
    have tail := (tendsto_order.mp limit).2 ε positive
    filter_upwards [tail] with n hn p
    have estimate := (contract p).apriori_dist_iterate_fixedPoint_le x n
    rw [point_unique T k contract p (contract p).fixedPoint_isFixedPt] at estimate
    have observed : dist (observe (point T k contract p)) (observe ((T p)^[n] x)) ≤
        dist ((T p)^[n] x) (point T k contract p) := by
      simpa only [NNReal.coe_one, one_mul, dist_comm] using
        nonexpansive.dist_le_mul ((T p)^[n] x) (point T k contract p)
    apply observed.trans_lt
    apply lt_of_le_of_lt _ hn
    apply estimate.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (displacement p) (pow_nonneg k.coe_nonneg n))
      (contract p).one_sub_K_pos.le
  exact uniform.continuous (Filter.Eventually.of_forall iterate_continuous).frequently

end LeanShared.ParameterizedContraction
