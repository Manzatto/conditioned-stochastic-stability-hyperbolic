module
public import LeanShared.Dynamics.ExpansiveBowenWindowShrinking
public import LeanShared.Dynamics.InvariantOrbitEnergy
public import LeanShared.Dynamics.OrbitEnergyConcatenation

/-! An invariant genuine Gibbs law has a positive Gibbs lower bound at
EVERY finer radius. A uniform expansivity buffer, actual invariance and the
bounded potential construct the new constant; no fine-scale lower source
or regularity of the ambient metric is assumed. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

set_option maxHeartbeats 2000000 in
theorem lower_gibbs_all_scales
    (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ρ P A : ℝ) (coarse : ρ ≤ c) (positiveA : 0 < A)
    (ν : Measure X) (invariant : MeasurePreserving T ν ν)
    (gibbs : ∀ n z, ENNReal.ofReal (A * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ}) :
    ∀ ε > 0, ∃ B > 0, ∀ n z,
      ENNReal.ofReal (B * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
        ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) < ε} := by
  intro ε positiveε
  obtain ⟨N, shrink⟩ := FiniteExpansiveWords.exists_window_shrinking T c expansive ε positiveε
  let B := A * Real.exp (-2 * (N : ℝ) * (‖φ‖ + P))
  refine ⟨B, mul_pos positiveA (Real.exp_pos _), fun n z => ?_⟩
  let z₀ := (T.symm : X → X)^[N] z
  let U := {x | ∀ j < n, dist (T^[j] x) (T^[j] z) < ε}
  let V := {x | ∀ j < n + 2 * N, dist (T^[j] x) (T^[j] z₀) ≤ ρ}
  have center : (T : X → X)^[N] z₀ = z := T.right_inv.iterate N z
  have opened : IsOpen U := by
    have openSet := isOpen_biInter_finset (s := Finset.range n)
      (f := fun j => {x | dist (T^[j] x) (T^[j] z) < ε})
      (fun j _ => isOpen_lt ((T.continuous.iterate j).dist continuous_const) continuous_const)
    convert openSet using 1
    ext x
    simp only [U, mem_ofPred_eq, mem_iInter, Finset.mem_range]
  have subset : V ⊆ ((T : X → X)^[N]) ⁻¹' U := by
    intro x hx j hj
    have small := shrink n x z₀ (fun i hi => (hx i hi).trans coarse) j hj
    rw [Nat.add_comm N j, iterate_add_apply, iterate_add_apply, center] at small
    exact small
  have mass : ν V ≤ ν U := by
    have bound := measure_mono (μ := ν) subset
    rw [(invariant.iterate N).measure_preimage opened.measurableSet.nullMeasurableSet] at bound
    exact bound
  have potentialLower (x : X) : -‖φ‖ ≤ φ x :=
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using φ.norm_coe_le_norm x)).1
  have energy : orbitSum T φ n z - 2 * (N : ℝ) * ‖φ‖ ≤ orbitSum T φ (n + 2 * N) z₀ := by
    have length : n + 2 * N = N + (n + N) := by omega
    rw [length, orbitSum_add T φ N (n + N), orbitSum_add T φ n N, center]
    have first := orbitSum_lower T φ univ (fun _ _ => mem_univ _) ‖φ‖
      (fun x _ => potentialLower x) N (mem_univ z₀)
    have last := orbitSum_lower T φ univ (fun _ _ => mem_univ _) ‖φ‖
      (fun x _ => potentialLower x) N (mem_univ (T^[n] z))
    linarith
  have exponent : -2 * (N : ℝ) * (‖φ‖ + P) + (orbitSum T φ n z - (n : ℝ) * P) ≤
      orbitSum T φ (n + 2 * N) z₀ - ((n + 2 * N : ℕ) : ℝ) * P := by
    push_cast
    nlinarith
  have exponential := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponent) positiveA.le
  rw [Real.exp_add] at exponential
  have compare : ENNReal.ofReal (B * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
      ENNReal.ofReal (A * Real.exp (orbitSum T φ (n + 2 * N) z₀ - ((n + 2 * N : ℕ) : ℝ) * P)) := by
    apply ENNReal.ofReal_le_ofReal
    simpa only [B, mul_assoc] using exponential
  exact compare.trans ((gibbs (n + 2 * N) z₀).trans mass)

end LeanShared.ThermodynamicDefinitions
