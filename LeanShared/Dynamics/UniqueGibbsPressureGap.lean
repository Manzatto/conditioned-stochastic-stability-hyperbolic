module

public import LeanShared.Dynamics.ProvedUniqueGibbsEquilibrium
public import LeanShared.Dynamics.GibbsFullSupport
public import LeanShared.Dynamics.ProperInvariantPressureGap

/-! The constructed unique Bowen Gibbs equilibrium has full support and
strictly dominates the pressure of every proper compact invariant subset.
All support and gap conclusions are outputs of the actual construction.
-/

public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_unique_full_support_equilibrium
    (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 18 * ε ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 9 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧
      ∃ ν : ProbabilityMeasure X, IsEquilibriumState T φ univ ν ∧ Ergodic T (ν : Measure X) ∧
        (∀ η : ProbabilityMeasure X, IsEquilibriumState T φ univ η → η = ν) ∧
        (∀ U : Set X, IsOpen U → U.Nonempty → 0 < (ν : Measure X) U) ∧
        ∀ K : Set X, IsClosed K → K.Nonempty → T '' K = K → K ≠ univ →
          pressure T φ K < pressure T φ univ := by
  obtain ⟨P, pressureP, A, positiveA, _B, _positiveB, ν, state, ergodic, unique, gibbs⟩ :=
    exists_unique_bowen_gibbs_equilibrium T c positiveC expansive φ ε D positiveε coarse bowen specification
  have fullSupport : ∀ U : Set X, IsOpen U → U.Nonempty → 0 < (ν : Measure X) U :=
    positive_open_of_lower_gibbs T c expansive φ (4 * ε) P A (by linarith) positiveA
      (ν : Measure X) ergodic.toMeasurePreserving (fun n z => (gibbs n z).1)
  refine ⟨P, pressureP, ν, state, ergodic, unique, fullSupport, ?_⟩
  intro K closed nonempty invariant proper
  exact pressure_lt_of_unique_full_support T c positiveC expansive φ ν unique fullSupport K closed nonempty invariant proper

end LeanShared.ThermodynamicDefinitions
