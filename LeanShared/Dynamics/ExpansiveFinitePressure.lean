module

public import LeanShared.Dynamics.ExpansiveSeparatedCardinality
public import LeanShared.Dynamics.PressureCardinalityBound
public import LeanShared.Dynamics.PressureLowerBound
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Tactic.Linarith

/-! Continuous potentials on nonempty compact expansive systems have finite
literal separated-set pressure. Neither a real pressure scalar nor pressure
finiteness is a background assumption in this theorem. -/
public noncomputable section
open Set
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

/-- A real pressure is constructed from compactness, expansivity and bounded
potential. No equilibrium existence or variational principle is used. -/
theorem finite_pressure_of_expansive_bounded (T : X ≃ₜ X) (c : ℝ) (hc : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y)
    (φ : X → ℝ) (B : ℝ) (bound : ∀ x, ‖φ x‖ ≤ B) :
    ∃ P : ℝ, pressure T φ univ=(P : EReal) := by
  obtain ⟨a,positive,counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c hc expansive
  have upper := pressure_le_of_card_bound (T := (T : X → X)) B
    (fun x => (le_abs_self (φ x)).trans (bound x)) a positive counts
  have lower := pressure_ge_of_lower_bound (T := (T : X → X)) (φ := φ) (-B) (fun x => by
    have hh := bound x
    rw [Real.norm_eq_abs,abs_le] at hh
    exact hh.1)
  have nottop : pressure T φ univ ≠ ⊤ := by
    intro hh
    rw [hh] at upper
    exact EReal.coe_ne_top _ (top_le_iff.mp upper)
  have notbot : pressure T φ univ ≠ ⊥ := by
    intro hh
    rw [hh] at lower
    exact EReal.coe_ne_bot _ (le_bot_iff.mp lower)
  exact ⟨(pressure T φ univ).toReal,(EReal.coe_toReal nottop notbot).symm⟩

/-- The continuous-potential compact-space theorem constructs its own
uniform norm bound. -/
theorem finite_pressure_of_expansive (T : X ≃ₜ X) (c : ℝ) (hc : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x=y)
    (φ : X → ℝ) (continuous : Continuous φ) :
    ∃ P : ℝ, pressure T φ univ=(P : EReal) := by
  let f := BoundedContinuousFunction.mkOfCompact (⟨φ,continuous⟩ : C(X,ℝ))
  exact finite_pressure_of_expansive_bounded T c hc expansive φ ‖f‖ f.norm_coe_le_norm

end LeanShared.ThermodynamicDefinitions
