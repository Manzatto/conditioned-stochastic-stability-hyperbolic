module

public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar

/-! The eventual-tail capture used by the support proof is derived from the
ordinary local unstable-set characterization, rather than supplied as that
proof's conclusion. The small fixed collar is chosen before the noise law. -/

@[expose] public section
open Set Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.LocalPositiveCollar
open LeanShared.ControlledPlaqueClosure
variable {X Ω : Type*}

theorem capture_of_local_backward_characterization
    (F : X × Ω → X) (G : Set X) (plaque : (ℤ → Ω) → Set X)
    (hlocal : ∀ (ω : ℤ → Ω) (b : ℕ → X), (∀ n, b n ∈ G) →
      (∀ n, F (b (n + 1), backwardNoise ω n) = b n) → b 0 ∈ plaque ω)
    (ω : ℤ → Ω) (b : ℕ → X)
    (step : ∀ n, F (b (n + 1), backwardNoise ω n) = b n)
    (tail : ∀ᶠ n in atTop, b n ∈ G) :
    ∃ j : ℕ, b j ∈ plaque (backwardShift ω j) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp tail
  have hnoise (n : ℕ) : backwardNoise (backwardShift ω N) n = backwardNoise ω (n + N) := by
    unfold backwardNoise backwardShift
    congr 1
    push_cast
    ring
  have hstep (n : ℕ) : F (b ((n + 1) + N), backwardNoise (backwardShift ω N) n) = b (n + N) := by
    rw [hnoise]
    simpa only [Nat.add_right_comm n 1 N] using step (n + N)
  have h := hlocal (backwardShift ω N) (fun n => b (n + N))
    (fun n => hN _ (Nat.le_add_left _ _)) hstep
  exact ⟨N, by simpa only [Nat.zero_add] using h⟩

end ConditionedStochasticStabilityHyperbolic.LocalPositiveCollar
