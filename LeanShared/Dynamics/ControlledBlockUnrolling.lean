module
public import LeanShared.Dynamics.BackwardBlockUnrolling
public import LeanShared.Dynamics.ControlledPlaqueClosure

/-! Exact return from a block-control backward orbit to the original
one-step control path. Future block controls are filled with the distinguished
zero control; every past control is the original specified control. -/
public noncomputable section
namespace LeanShared.ControlledBlockUnrolling
open FiniteJetComposition ControlledPlaqueClosure BackwardBlockUnrolling

@[expose] def blockPath {Ω : Type*} (zero : Ω) (N : ℕ) (path : ℤ → Ω) : ℤ → ℕ → Ω :=
  completeBackwardNoise (fun _ => zero)
    (fun n j => backwardNoise path (N * (n + 1) - 1 - j))

theorem block_control {Ω : Type*} (zero : Ω) (N : ℕ) (path : ℤ → Ω) (n j : ℕ) :
    backwardNoise (blockPath zero N path) n j =
      backwardNoise path (N * (n + 1) - 1 - j) := by
  exact congrFun (backwardNoise_complete (fun _ => zero)
    (fun n j => backwardNoise path (N * (n + 1) - 1 - j)) n) j

theorem exists_one_step_orbit {X Ω : Type*} (F : X × Ω → X) (zero : Ω)
    (N : ℕ) (positive : 0 < N) (path : ℤ → Ω) (B : ℕ → X)
    (step : ∀ n, word (fun j x => F (x, backwardNoise (blockPath zero N path) n j)) N
      (B (n + 1)) = B n) :
    ∃ b : ℕ → X, b 0 = B 0 ∧
      (∀ n, F (b (n + 1), backwardNoise path n) = b n) ∧
      (∀ n, b (N * n) = B n) ∧
      ∀ m, b m = word (fun j x => F (x, backwardNoise (blockPath zero N path) (m / N) j))
        (N - m % N) (B (m / N + 1)) := by
  let f : ℕ → X → X := fun n x => F (x, backwardNoise path n)
  have blocks (n : ℕ) : word (block f N n) N (B (n + 1)) = B n := by
    change word (fun j x => F (x, backwardNoise path (N * (n + 1) - 1 - j)))
      N (B (n + 1)) = B n
    simpa only [block_control] using step n
  refine ⟨unroll f N B, BackwardBlockUnrolling.zero f N B blocks,
    BackwardBlockUnrolling.one_step f N positive B blocks,
    BackwardBlockUnrolling.at_block f N positive B blocks, ?_⟩
  intro m
  change word (fun j x => F (x, backwardNoise path (N * (m / N + 1) - 1 - j)))
    (N - m % N) (B (m / N + 1)) = _
  simp only [block_control]

end LeanShared.ControlledBlockUnrolling
