module

public import LeanShared.Dynamics.GibbsUniformOpenIntersection
public import LeanShared.Dynamics.GibbsLowerScaleExtension
public import LeanShared.Dynamics.UniformOpenIntersectionErgodicity

/-! The actual invariant Gibbs measure of a compact expansive system with
point specification is ergodic. Fine lower cylinders are constructed from
invariance and expansivity; uniform correlations are proved by weighted
gluing, and regular approximation rules out invariant components. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1600000 in
theorem ergodic_of_bowen_gibbs (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ν : Measure X) [IsFiniteMeasure ν]
    [ν.InnerRegularCompactLTTop] [ν.OuterRegular]
    (invariant : MeasurePreserving T ν ν) (ρ A B P D : ℝ)
    (positive : 0 < ρ) (coarse : ρ ≤ c) (positiveA : 0 < A) (positiveB : 0 < B)
    (gibbs : ∀ n z,
      ENNReal.ofReal (A * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
        ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ} ∧
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ} ≤
        ENNReal.ofReal (B * Real.exp (orbitSum T φ n z - (n : ℝ) * P)))
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ρ) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    Ergodic T ν := by
  let ε := ρ / 12
  have positiveε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨A', positiveA', lower⟩ := lower_gibbs_all_scales T c expansive φ ρ P A coarse
    positiveA ν invariant (fun n z => (gibbs n z).1) ε positiveε
  obtain ⟨gap, positiveGap, tracing⟩ := specification (3 * ε) (by positivity)
  have upper : ∀ n z, ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 9 * ε} ≤
      ENNReal.ofReal (B * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) := by
    intro n z
    have included : {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 9 * ε} ⊆
        {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ} := by
      intro x close j hj
      exact (close j hj).trans (by dsimp [ε]; linarith)
    exact (measure_mono included).trans (gibbs n z).2
  obtain ⟨C, positiveConstant, correlation⟩ := uniform_open_intersection_of_gibbs T c positiveC
    expansive φ ν invariant ε A' B P D positiveε (by dsimp [ε]; linarith)
    positiveA' positiveB gap positiveGap tracing
    (fun n x y close => bowen (n + 1) x y (fun j hj =>
      (close j (by omega)).trans (by dsimp [ε]; linarith))) lower upper
  exact LeanShared.ergodic_of_open_intersections T ν invariant C positiveConstant correlation

end LeanShared.ThermodynamicDefinitions
