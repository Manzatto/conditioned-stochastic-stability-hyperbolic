module

public import LeanShared.Dynamics.PressureBoundedPerturbation
import Mathlib.Tactic.Linarith

/-! Real pressure of a positive logarithmic envelope is constructed from
finite reference pressure and the actual pointwise logarithmic estimate. -/
public noncomputable section
open Set
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X} {φ ψ : X → ℝ}

theorem pressure_mono (invariant : MapsTo T K K) (bound : ∀ x ∈ K, φ x ≤ ψ x) :
    pressure T φ K ≤ pressure T ψ K := by
  simpa only [EReal.coe_zero,add_zero] using pressure_le_add invariant 0 (by simpa only [add_zero] using bound)

/-- Construct an actual finite scalar for a monotone bounded perturbation,
with sharp pressure bounds inherited from the finite reference scalar. -/
theorem finite_pressure_of_monotone_perturbation (invariant : MapsTo T K K)
    (P δ : ℝ) (finite : pressure T φ K=(P : EReal)) (hδ : 0 ≤ δ)
    (lower : ∀ x ∈ K, φ x ≤ ψ x) (upper : ∀ x ∈ K, ψ x ≤ φ x+δ) :
    ∃ Q : ℝ, pressure T ψ K=(Q : EReal) ∧ P ≤ Q ∧ Q ≤ P+δ := by
  obtain ⟨Q,identity,_,bound⟩ := finite_pressure_of_bounded_difference invariant P δ finite upper
    (fun x hx => (lower x hx).trans (le_add_of_nonneg_right hδ))
  refine ⟨Q,identity,?_,bound⟩
  have order := pressure_mono invariant lower
  rw [finite,identity] at order
  exact EReal.coe_le_coe_iff.mp order

/-- Literal logarithmic weight envelopes have finite pressure without a
separately supplied envelope-pressure scalar or identity. The Jacobian term
is arbitrary because it cancels in the comparison. -/
theorem finite_log_envelope_pressure (invariant : MapsTo T K K)
    (g w J : X → ℝ) (P δ : ℝ)
    (finite : pressure T (fun x => Real.log (g x)-J x) K=(P : EReal))
    (hδ : 0 ≤ δ)
    (logarithms : ∀ x ∈ K, 0 ≤ Real.log (w x)-Real.log (g x) ∧
      Real.log (w x)-Real.log (g x) ≤ δ) :
    ∃ Q : ℝ, pressure T (fun x => Real.log (w x)-J x) K=(Q : EReal) ∧
      P ≤ Q ∧ Q ≤ P+δ := by
  apply finite_pressure_of_monotone_perturbation invariant P δ finite hδ
  · intro x hx
    linarith [(logarithms x hx).1]
  · intro x hx
    linarith [(logarithms x hx).2]

end LeanShared.ThermodynamicDefinitions
