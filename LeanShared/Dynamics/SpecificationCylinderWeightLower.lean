module
public import LeanShared.Dynamics.PrescribedMiddleWeightedGluing
public import LeanShared.Dynamics.SpanningMiddleWeightLower

/-! Actual specification gives a lower weighted mass INSIDE a prescribed
middle cylinder of any actual separated spanning family. The tracing family
and its injective cover-center map are both constructed internally. -/
public noncomputable section
open Set
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 2400000 in
theorem specification_cylinder_weight_lower
    (T : X → X) (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ)
    (bowen : ∀ h x y, (∀ j < h, dist (T^[j] x) (T^[j] y) < 3 * ε) →
      |orbitSum T φ h x - orbitSum T φ h y| ≤ D) :
    ∃ gap : ℕ, 0 < gap ∧ ∀ n k m : ℕ, ∀ z : X, ∀ s t a : Finset X,
      Separated T univ (n + 1) (9 * ε) s →
      Separated T univ (m + 1) (9 * ε) t →
      (∀ x : X, ∃ y ∈ a, ∀ j < n + gap + k + gap + m + 1,
        dist (T^[j] x) (T^[j] y) < ε) →
      Real.exp (orbitSum T φ (k + 1) z - 4 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) *
        (∑ x ∈ s, Real.exp (orbitSum T φ (n + 1) x)) *
        (∑ y ∈ t, Real.exp (orbitSum T φ (m + 1) y)) ≤
          ∑ w ∈ a.filter (fun w => ∀ j < k + 1,
            dist (T^[n + gap + j] w) (T^[j] z) < 4 * ε),
              Real.exp (orbitSum T φ (n + gap + k + gap + m + 1) w) := by
  classical
  obtain ⟨gap, positiveGap, trace⟩ := three_segments_of_point_specification T specification
    (3 * ε) (by positivity)
  refine ⟨gap, positiveGap, fun n k m z s t a first last spans => ?_⟩
  have scale : 3 * (3 * ε) = 9 * ε := by ring
  obtain ⟨q, separatedQ, middle, weighted⟩ := prescribed_middle_weighted_gluing T φ
    (3 * ε) D (by positivity) gap positiveGap trace bowen n k m z s t
    (by simpa only [scale] using first) (by simpa only [scale] using last)
  have cover := spanning_middle_weight_lower T φ (n + gap + k + gap + m + 1)
    (n + gap) (k + 1) (by omega) z ε (3 * ε) D positiveε a q separatedQ spans
    (fun x hx j hj => middle x hx j (by omega))
    (fun x y close => bowen _ x y (fun j hj => (close j hj).trans_le (by linarith)))
  have weighted' := mul_le_mul_of_nonneg_left weighted (Real.exp_nonneg (-D))
  have coefficient : Real.exp (orbitSum T φ (k + 1) z - 4 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) =
      Real.exp (-D) * Real.exp (orbitSum T φ (k + 1) z - 3 * D - 2 * (gap - 1 : ℕ) * ‖φ‖) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [coefficient, mul_assoc, mul_assoc] at ⊢
  have bound := weighted'.trans cover
  have larger : ε + 3 * ε = 4 * ε := by ring
  simpa only [larger, mul_assoc] using bound

end LeanShared.ThermodynamicDefinitions
