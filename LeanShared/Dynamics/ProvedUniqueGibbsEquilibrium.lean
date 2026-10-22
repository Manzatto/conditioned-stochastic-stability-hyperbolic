module
public import LeanShared.Dynamics.ProvedErgodicGibbsEquilibrium
public import LeanShared.Dynamics.BowenGibbsErgodicity
public import LeanShared.Dynamics.EquilibriumGibbsAbsoluteContinuity
public import Mathlib.Dynamics.Ergodic.Extreme

/-! The same constructed two-sided Gibbs equilibrium is ergodic; its
probability is retained rather than replaced by an ergodic component. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 2400000 in
theorem exists_unique_bowen_gibbs_equilibrium
    (T : X ≃ₜ X) (c₀ : ℝ) (positive₀ : 0 < c₀)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c₀ ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c₀) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 18 * ε ≤ c₀)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 9 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ A > 0, ∃ B > 0,
      ∃ ν : ProbabilityMeasure X, IsEquilibriumState T φ univ ν ∧ Ergodic T (ν : Measure X) ∧
      (∀ η : ProbabilityMeasure X, IsEquilibriumState T φ univ η → η = ν) ∧
        ∀ n : ℕ, ∀ z : X,
          ENNReal.ofReal (A * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
            (ν : Measure X) {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 4 * ε} ∧
          (ν : Measure X) {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 4 * ε} ≤
            ENNReal.ofReal (B * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) := by
  obtain ⟨P, pressureP, A, positiveA, B, positiveB, ν, state, ergodic, gibbs⟩ :=
    exists_ergodic_bowen_gibbs_equilibrium T c₀ positive₀ expansive φ ε D positiveε coarse bowen specification
  have unique (η : ProbabilityMeasure X) (stateη : IsEquilibriumState T φ univ η) : η = ν := by
    obtain ⟨A', positiveA', lower⟩ := lower_gibbs_all_scales T c₀ expansive φ (4 * ε) P A
      (by linarith) positiveA (ν : Measure X) ergodic.toMeasurePreserving
      (fun n z => (gibbs n z).1) (ε / 3) (by positivity)
    have absolutely := equilibrium_absolutelyContinuous_gibbs T c₀ positive₀ expansive φ η ν stateη
      ergodic.toMeasurePreserving P A' D ε pressureP positiveA' positiveε (by linarith)
      (fun n x y close => bowen n x y (fun j hj => (close j hj).trans_le (by linarith))) lower
    apply ProbabilityMeasure.toMeasure_injective
    exact ergodic.eq_of_absolutelyContinuous ⟨stateη.1, stateη.2.1⟩ absolutely
  exact ⟨P, pressureP, A, positiveA, B, positiveB, ν, state, ergodic, unique, gibbs⟩

end LeanShared.ThermodynamicDefinitions
