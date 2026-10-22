module
public import LeanShared.Dynamics.ControlledBlockUnrolling

/-! Passing an original control path to its block path is continuous in the
product topology. No continuity of the noisy family in its scale is used. -/
public noncomputable section
namespace LeanShared.ControlledBlockUnrolling
open ControlledPlaqueClosure

 theorem continuous_blockPath {Ω : Type*} [TopologicalSpace Ω]
    (zero : Ω) (N : ℕ) : Continuous (blockPath zero N : (ℤ → Ω) → ℤ → ℕ → Ω) := by
  apply continuous_pi
  intro k
  apply continuous_pi
  intro j
  by_cases negative : k < 0
  · simpa only [blockPath, completeBackwardNoise, ite_eq_left negative, backwardNoise] using
      (continuous_apply (-(N * (((-k - 1).toNat) + 1) - 1 - j : ℕ) - 1 : ℤ))
  · simpa only [blockPath, completeBackwardNoise, ite_eq_right negative] using
      (continuous_const : Continuous (fun _ : ℤ → Ω => zero))

end LeanShared.ControlledBlockUnrolling
