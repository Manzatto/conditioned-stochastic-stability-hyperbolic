module
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Algebra.Order.Field

/-! Quantitative parameter dependence of actual contraction fixed points. Only
continuity at the reference fixed point is needed; no uniform continuity in the
whole graph space is assumed. This is a graph-transform primitive, not a
stable-manifold existence hypothesis. -/
public noncomputable section
namespace LeanShared.ParameterizedContraction
open Filter
open scoped Topology NNReal

def point {P X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : P → X → X) (k : ℝ≥0) (contract : ∀ p, ContractingWith k (T p)) (p : P) : X :=
  (contract p).fixedPoint (T p)

theorem point_fixed {P X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : P → X → X) (k : ℝ≥0) (contract : ∀ p, ContractingWith k (T p)) (p : P) :
    T p (point T k contract p) = point T k contract p :=
  (contract p).fixedPoint_isFixedPt

theorem point_unique {P X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : P → X → X) (k : ℝ≥0) (contract : ∀ p, ContractingWith k (T p))
    (p : P) {x : X} (fixed : T p x = x) : x = point T k contract p :=
  (contract p).fixedPoint_unique fixed

theorem point_distance {P X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : P → X → X) (k : ℝ≥0) (contract : ∀ p, ContractingWith k (T p)) (p q : P) :
    dist (point T k contract p) (point T k contract q) ≤
      dist (T p (point T k contract q)) (T q (point T k contract q)) / (1 - k) := by
  have estimate := (contract p).dist_fixedPoint_le (point T k contract q)
  change dist (point T k contract q) (point T k contract p) ≤ _ at estimate
  calc
    _ = dist (point T k contract q) (point T k contract p) := dist_comm _ _
    _ ≤ _ := estimate
    _ = _ := by rw [point_fixed T k contract q, dist_comm]

theorem continuousAt_point {P X : Type*} [TopologicalSpace P]
    [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : P → X → X) (k : ℝ≥0) (contract : ∀ p, ContractingWith k (T p)) (q : P)
    (continuous : ContinuousAt (fun p => T p (point T k contract q)) q) :
    ContinuousAt (point T k contract) q := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (point_distance T k contract · q)
  have bound := (continuous.dist (continuousAt_const (y := T q (point T k contract q)))).div_const (1 - (k : ℝ))
  simpa only [point_fixed T k contract q, dist_self, zero_div] using bound

theorem continuous_point {P X : Type*} [TopologicalSpace P]
    [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (T : P → X → X) (k : ℝ≥0) (contract : ∀ p, ContractingWith k (T p))
    (continuous : ∀ x, Continuous (fun p => T p x)) :
    Continuous (point T k contract) :=
  continuous_iff_continuousAt.mpr fun q =>
    continuousAt_point T k contract q (continuous (point T k contract q)).continuousAt

end LeanShared.ParameterizedContraction
