module

public import LeanShared.Dynamics.GibbsCylinderPacking
public import Mathlib.MeasureTheory.Measure.Real

/-! A Gibbs upper estimate turns any actual finite spanning family of a
prescribed set into a lower bound for its normalized orbit-weight sum.
The measure and the orbit weights are the original objects throughout. -/
public noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem gibbs_cover_real_weight (T : X → X) (φ : X → ℝ) (ν : Measure X)
    [IsFiniteMeasure ν] (K : Set X) (s : Finset X) (n : ℕ) (ρ H P : ℝ)
    (nonnegative : 0 ≤ H)
    (cover : ∀ x ∈ K, ∃ y ∈ s, ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ ρ)
    (upper : ∀ y ∈ s, ν {x | ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ ρ} ≤
      ENNReal.ofReal (H * Real.exp (orbitSum T φ n y - (n : ℝ) * P))) :
    ν.real K ≤ H * Real.exp (-(n : ℝ) * P) *
      ∑ y ∈ s, Real.exp (orbitSum T φ n y) := by
  have bound := gibbs_cover_weight T φ ν K s n ρ H P cover upper
  have identity : (∑ y ∈ s, ENNReal.ofReal
      (H * Real.exp (orbitSum T φ n y - (n : ℝ) * P))) =
      ENNReal.ofReal (H * Real.exp (-(n : ℝ) * P) *
        ∑ y ∈ s, Real.exp (orbitSum T φ n y)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg nonnegative (Real.exp_nonneg _))]
    congr 1
    have negative : -((n : ℝ) * P) = -(n : ℝ) * P := by ring
    simp_rw [sub_eq_add_neg, Real.exp_add, negative]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [identity] at bound
  have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top bound
  rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg nonnegative (Real.exp_nonneg _))
    (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)))] at realBound
  exact realBound

end LeanShared.ThermodynamicDefinitions
