module

public import LeanShared.Dynamics.GibbsLowerScaleExtension

/-! The actual invariant lower Gibbs law has positive mass on every
nonempty open set.  Fine cylinders are produced from expansivity and
invariance, rather than assumed as an additional support property. -/

public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem positive_open_of_lower_gibbs (T : X ≃ₜ X) (c : ℝ)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) (ρ P A : ℝ) (coarse : ρ ≤ c) (positiveA : 0 < A)
    (ν : Measure X) (invariant : MeasurePreserving T ν ν)
    (gibbs : ∀ n z, ENNReal.ofReal (A * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
      ν {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ ρ})
    (U : Set X) (opened : IsOpen U) (nonempty : U.Nonempty) : 0 < ν U := by
  obtain ⟨z, member⟩ := nonempty
  obtain ⟨ε, positiveε, inside⟩ := Metric.isOpen_iff.mp opened z member
  obtain ⟨B, positiveB, fine⟩ := lower_gibbs_all_scales T c expansive φ ρ P A coarse positiveA ν invariant gibbs ε positiveε
  have inclusion : {x | ∀ j < 1, dist (T^[j] x) (T^[j] z) < ε} ⊆ U := by
    intro x hx
    apply inside
    have close := hx 0 (by omega)
    simpa only [iterate_zero_apply, Metric.mem_ball, dist_comm] using close
  have positiveWeight : 0 < ENNReal.ofReal (B * Real.exp (orbitSum T φ 1 z - (1 : ℝ) * P)) :=
    ENNReal.ofReal_pos.mpr (mul_pos positiveB (Real.exp_pos _))
  have fineOne := fine 1 z
  simp only [Nat.cast_one] at fineOne
  exact (positiveWeight.trans_le fineOne).trans_le (measure_mono inclusion)

end LeanShared.ThermodynamicDefinitions
