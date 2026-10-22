module
public import LeanShared.Dynamics.ControlledBlockUnrolling
public import LeanShared.Dynamics.BackwardBlockSampling

/-! Exact sampling and time shifting retain the original controls, including
all intermediate steps, before any plaque or shadowing construction. -/
public noncomputable section
namespace LeanShared.ControlledBlockSampling
open FiniteJetComposition ControlledPlaqueClosure ControlledBlockUnrolling

theorem backwardNoise_shift {Ω : Type*} (path : ℤ → Ω) (j n : ℕ) :
    backwardNoise (backwardShift path j) n = backwardNoise path (n + j) := by
  unfold backwardNoise backwardShift
  congr 1
  omega

theorem shifted_step {X Ω : Type*} (F : X × Ω → X) (path : ℤ → Ω)
    (b : ℕ → X) (step : ∀ n, F (b (n + 1), backwardNoise path n) = b n) (j n : ℕ) :
    F (b (j + (n + 1)), backwardNoise (backwardShift path j) n) = b (j + n) := by
  rw [backwardNoise_shift, Nat.add_comm n j]
  simpa only [Nat.add_assoc] using step (j + n)

theorem sampled_step {X Ω : Type*} (F : X × Ω → X) (zero : Ω)
    (path : ℤ → Ω) (b : ℕ → X)
    (step : ∀ n, F (b (n + 1), backwardNoise path n) = b n) (N n : ℕ) :
    word (fun j x => F (x, backwardNoise (blockPath zero N path) n j)) N
      (b (N * (n + 1))) = b (N * n) := by
  have result := BackwardBlockSampling.sampled_step (fun n x => F (x, backwardNoise path n)) b step N n
  change word (fun j x => F (x, backwardNoise path (N * (n + 1) - 1 - j))) N
    (b (N * (n + 1))) = b (N * n) at result
  simpa only [block_control] using result

end LeanShared.ControlledBlockSampling
