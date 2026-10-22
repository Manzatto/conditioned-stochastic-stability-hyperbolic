module
public import Mathlib.Topology.MetricSpace.Basic

/-! Ordinary two-segment specification constructs three-segment tracing
with the same fixed gap, before all segment lengths and reference points.
This is the prescribed-middle gluing needed for the lower Gibbs estimate. -/
public noncomputable section
open Function
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

theorem three_segments_of_point_specification (T : X → X)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ)
    (ε : ℝ) (positiveε : 0 < ε) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n k m : ℕ, ∀ x z y : X, ∃ w : X,
      (∀ j ≤ n, dist (T^[j] w) (T^[j] x) < ε) ∧
      (∀ j ≤ k, dist (T^[n + gap + j] w) (T^[j] z) < ε) ∧
      ∀ j ≤ m, dist (T^[n + gap + k + gap + j] w) (T^[j] y) < ε := by
  obtain ⟨gap, positiveGap, trace⟩ := specification (ε / 2) (by positivity)
  refine ⟨gap, positiveGap, fun n k m x z y => ?_⟩
  obtain ⟨v, first, middle⟩ := trace n k x z
  obtain ⟨w, initial, last⟩ := trace (n + gap + k) m v y
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j hj
    have triangle := dist_triangle (T^[j] w) (T^[j] v) (T^[j] x)
    have one := initial j (by omega)
    have two := first j hj
    linarith
  · intro j hj
    have triangle := dist_triangle (T^[n + gap + j] w) (T^[n + gap + j] v) (T^[j] z)
    have one := initial (n + gap + j) (by omega)
    have two := middle j hj
    linarith
  · intro j hj
    exact (last j hj).trans (by linarith)

end LeanShared.ThermodynamicDefinitions
