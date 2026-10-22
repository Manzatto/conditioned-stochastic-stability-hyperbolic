module

public import LeanShared.Dynamics.RobustFiniteIsolation
import Mathlib.Tactic.Linarith

/-!
# Robust absorption into the fixed open region

A deterministic finite entrance into the open absorbing set survives uniformly
for every small nonautonomous noise word. The region itself is never shifted.
This is the geometric finite-absorption assertion of global-global item (iv).
-/

@[expose] public section
open Set Metric
namespace ConditionedStochasticStabilityHyperbolic.Global.RobustAbsorption
variable {X Ω : Type*} [MetricSpace X]

/-- Finite deterministic entrance into the fixed open absorption region is
robust for every control sequence, including different controls at every step. -/
theorem exists_small_noise_finite_absorption
    (T : X → X) (hT : UniformContinuous T) (A : Set X) (hA : IsOpen A)
    (x : X) (N : ℕ) (henter : T^[N] x ∈ A)
    (F : ℝ → X × Ω → X) {c : ℝ} (hc : 0 ≤ c)
    (hnoise : ∀ ε > 0, ∀ z ω, dist (F ε (z, ω)) (T z) ≤ c * ε) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ → ∀ controls : ℕ → Ω,
      LeanShared.nonautonomousOrbit (fun n z => F ε (z, controls n)) x N ∈ A := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hA _ henter
  obtain ⟨δ, hδ, hclose⟩ := LeanShared.exists_uniform_finite_orbit_closeness hT N hr
  have hc1 : 0 < c + 1 := by linarith
  refine ⟨δ / (c + 1), div_pos hδ hc1, ?_⟩
  intro ε hε hsmall controls
  have hstep : c * ε < δ := by
    have hh : ε * (c + 1) < δ := (lt_div_iff₀ hc1).mp hsmall
    nlinarith
  apply hball
  exact hclose (LeanShared.nonautonomousOrbit (fun n z => F ε (z, controls n)) x)
    (fun n _ => (hnoise ε hε _ _).trans_lt hstep) N le_rfl

end ConditionedStochasticStabilityHyperbolic.Global.RobustAbsorption
