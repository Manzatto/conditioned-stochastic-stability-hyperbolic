module
public import LeanShared.Dynamics.PressureCoboundary

/-! Uniform endpoint coboundary costs for actual finite separated partitions.
The cost does not grow with the word length. -/
public noncomputable section
namespace LeanShared.ThermodynamicDefinitions
open Set Function
open scoped BigOperators
variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X} {φ ψ u : X → ℝ}

theorem separatedPartitionSum_le_of_orbit_bound (C : ℝ)
    (bound : ∀ n x, x ∈ K → orbitSum T φ n x ≤ orbitSum T ψ n x + C)
    (n : ℕ) (ε : ℝ) : separatedPartitionSum T φ K n ε ≤
      ENNReal.ofReal (Real.exp C) * separatedPartitionSum T ψ K n ε := by
  classical
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun hs => ?_
  calc
    _ ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (Real.exp (orbitSum T ψ n x)) := by
      apply Finset.sum_le_sum
      intro x hx
      have h := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (bound n x (hs.1 x hx)))
      rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
      simpa only [mul_comm] using h
    _ = ENNReal.ofReal (Real.exp C) * ∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T ψ n x)) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup_of_le s (by simp only [iSup_pos hs]; exact le_rfl))

theorem separatedPartitionSum_coboundary_lower (invariant : MapsTo T K K) (B : ℝ)
    (bounded : ∀ x ∈ K, |u x| ≤ B)
    (same : ∀ x ∈ K, φ x = ψ x + u x - u (T x)) (n : ℕ) (ε : ℝ) :
    separatedPartitionSum T ψ K n ε ≤ ENNReal.ofReal (Real.exp (2 * B)) *
      separatedPartitionSum T φ K n ε := by
  apply separatedPartitionSum_le_of_orbit_bound
  intro m x hx
  have identity := orbitSum_coboundary invariant same m hx
  have first := (abs_le.mp (bounded x hx)).1
  have second := (abs_le.mp (bounded _ (invariant.iterate m hx))).2
  linarith

end LeanShared.ThermodynamicDefinitions
