module

public import ConditionedStochasticStabilityHyperbolic.Global.RobustAbsorption

/-! # Literal HG2(iv): absorption for every control, including time-zero entry

The entrance time takes its infimum over strictly positive times, as in the
manuscript. If deterministic entrance is supplied at time zero, forward
invariance gives entrance at time one. Robust finite orbit control then gives
one bound for every noise sequence, without an almost-sure qualification.
-/
@[expose] public noncomputable section
open Set Metric Function
namespace ConditionedStochasticStabilityHyperbolic.Global.GlobalAbsorptionEveryControl
variable {X Ω : Type*} [MetricSpace X]

/-- First strictly positive entrance, with infinity when no entrance occurs. -/
def positiveEntranceTime (orbit : ℕ → X) (A : Set X) : WithTop ℕ :=
  ⨅ n : ℕ, ⨅ (_ : 0 < n ∧ orbit n ∈ A), (n : WithTop ℕ)

/-- The actual every-sequence absorption conclusion of global-global(iv).
The source permits deterministic entrance at time zero. -/
theorem exists_uniform_every_control_absorption
    (T : X → X) (hT : UniformContinuous T) (A : Set X) (hA : IsOpen A)
    (hAfwd : MapsTo T A A) (x : X) (henter : ∃ n : ℕ, T^[n] x ∈ A)
    (F : ℝ → X × Ω → X) {c : ℝ} (hc : 0 ≤ c)
    (hnoise : ∀ ε > 0, ∀ z ω, dist (F ε (z, ω)) (T z) ≤ c * ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ controls : ℕ → Ω,
        positiveEntranceTime
          (LeanShared.nonautonomousOrbit (fun n z => F ε (z, controls n)) x) A ≤ (N : WithTop ℕ) := by
  obtain ⟨n, hn⟩ := henter
  have hnext : T^[n + 1] x ∈ A := by
    rw [iterate_succ_apply']
    exact hAfwd hn
  obtain ⟨ε₀, hε₀, hall⟩ := RobustAbsorption.exists_small_noise_finite_absorption
    T hT A hA x (n + 1) hnext F hc hnoise
  refine ⟨n + 1, Nat.succ_pos n, ε₀, hε₀, ?_⟩
  intro ε hε hsmall controls
  unfold positiveEntranceTime
  exact iInf_le_of_le (n + 1) (iInf_le_of_le ⟨Nat.succ_pos n, hall ε hε hsmall controls⟩ le_rfl)

end ConditionedStochasticStabilityHyperbolic.Global.GlobalAbsorptionEveryControl
