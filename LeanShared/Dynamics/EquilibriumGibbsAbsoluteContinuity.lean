module

public import LeanShared.Dynamics.PositiveEquilibriumRelativePartitions
public import LeanShared.Dynamics.BoundedBowenRelativeEntropyAC

/-! Every literal equilibrium probability is absolutely continuous with
respect to an invariant Gibbs reference. Actual finite Bowen partitions
and their uniform relative-entropy bounds are constructed internally. -/
public noncomputable section
open Set MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 1200000 in
theorem equilibrium_absolutelyContinuous_gibbs (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (μ ν : ProbabilityMeasure X) (state : IsEquilibriumState T φ univ μ)
    (invariantν : MeasurePreserving T (ν : Measure X) ν)
    (P A D ε : ℝ) (pressureP : pressure T φ univ = (P : EReal))
    (positiveA : 0 < A) (positive : 0 < ε) (coarse : 2 * ε ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (lower : ∀ n y, ENNReal.ofReal (A * Real.exp (orbitSum T φ n y - (n : ℝ) * P)) ≤
      (ν : Measure X) {x | ∀ j < n, dist (T^[j] x) (T^[j] y) < ε / 3}) :
    (μ : Measure X) ≪ (ν : Measure X) := by
  apply absolutelyContinuous_of_bowen_relative_bound T c expansive μ ν
    ⟨state.1, state.2.1⟩ invariantν (D - Real.log A)
  intro n
  obtain ⟨k, hk, Q, positiveQ, mesh, bound⟩ := exists_positive_equilibrium_relative_partitions
    T c positiveC expansive φ μ ν state P A D ε pressureP positiveA positive coarse bowen lower n
  exact ⟨k, hk, Q, positiveQ, fun i x y hx hy j hj =>
    (mesh i x y hx hy j hj).le.trans coarse, bound⟩

end LeanShared.ThermodynamicDefinitions
