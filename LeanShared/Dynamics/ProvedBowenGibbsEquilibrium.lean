module
public import LeanShared.Dynamics.SpanningGibbsApproximations
public import LeanShared.Dynamics.CesaroLowerCylinderBoundaryLoss
public import LeanShared.Dynamics.GibbsUpperScaleExtension
public import LeanShared.Dynamics.UpperGibbsEquilibrium

/-! Compact expansivity, actual point specification and Bowen distortion
CONSTRUCT a genuine two-sided Gibbs equilibrium probability. Upper and lower
bounds use the SAME spanning Gibbs sequence, SAME Cesaro weak limit, SAME
closed Bowen cylinders and actual pressure. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 3200000 in
theorem exists_bowen_gibbs_equilibrium
    (T : X ≃ₜ X) (c₀ : ℝ) (positive₀ : 0 < c₀)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c₀ ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c₀) → x = y)
    (φ : X →ᵇ ℝ) (ε D : ℝ) (positiveε : 0 < ε) (coarse : 18 * ε ≤ c₀)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < 9 * ε) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D)
    (specification : ∀ δ > 0, ∃ gap : ℕ, 0 < gap ∧
      ∀ n m : ℕ, ∀ x y : X, ∃ z : X,
        (∀ j ≤ n, dist (T^[j] z) (T^[j] x) < δ) ∧
        ∀ j ≤ m, dist (T^[n + gap + j] z) (T^[j] y) < δ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∃ A > 0, ∃ B > 0,
      ∃ ν : ProbabilityMeasure X, IsEquilibriumState T φ univ ν ∧
        ∀ n : ℕ, ∀ z : X,
          ENNReal.ofReal (A * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
            (ν : Measure X) {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 4 * ε} ∧
          (ν : Measure X) {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 4 * ε} ≤
            ENNReal.ofReal (B * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) := by
  classical
  obtain ⟨P, pressureP, gap, positiveGap, Hu, positiveHu, Hl, positiveHl, σ, upper, lower⟩ :=
    exists_spanning_gibbs_approximations T c₀ positive₀ expansive φ ε D positiveε coarse bowen specification
  obtain ⟨ν, _, ι, mono, weak⟩ :=
    isSeqCompact_univ (fun n => mem_univ (CesaroProbability.probabilityMeasure T (σ n) n))
  have invariant := CesaroProbability.invariant_of_limit T T.continuous σ ν ι mono weak
  have fineUpper : ∀ k z U, IsOpen U →
      (∀ x ∈ U, ∀ j < k, dist (T^[j] x) (T^[j] z) < ε / 3) →
      (ν : Measure X) U ≤ ENNReal.ofReal (Hu * Real.exp (orbitSum T φ k z - (k : ℝ) * P)) := by
    intro k z U openU inside
    apply CesaroProbability.cylinder_bound_of_limit T T.continuous.measurable σ ν ι mono weak k
      (Hu * Real.exp (orbitSum T φ k z - (k : ℝ) * P)) (by positivity) U openU
    intro N j hj positiveJ interior
    have mass := upper N k z U openU.measurableSet inside j hj positiveJ interior
    have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top mass
    rw [ENNReal.toReal_ofReal (mul_nonneg positiveHu.le (Real.exp_nonneg _))] at realBound
    exact realBound
  have state := equilibrium_of_upper_gibbs T c₀ positive₀ expansive φ (ε / 3) Hu P
    (by positivity) positiveHu pressureP ν invariant fineUpper
  obtain ⟨B, positiveB, coarseUpper⟩ := upper_gibbs_scale_extension T c₀ positive₀ expansive φ
    (ε / 3) (4 * ε) Hu D P (by positivity) (by positivity) positiveHu (by linarith)
    (ν : Measure X) fineUpper (fun n x y close => bowen n x y
      (fun j hj => (close j hj).trans_le (by linarith)))
  let A := min Hl 1
  have positiveA : 0 < A := lt_min positiveHl zero_lt_one
  refine ⟨P, pressureP, A, positiveA, B, positiveB, ν, state, fun n z => ⟨?_, coarseUpper n z⟩⟩
  by_cases zero : n = 0
  · subst n
    have emptyWord : {x : X | ∀ j < 0, dist (T^[j] x) (T^[j] z) ≤ 4 * ε} = univ := by
      ext x
      simp
    rw [emptyWord, measure_univ]
    simp only [orbitSum, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul,
      sub_self, Real.exp_zero, mul_one]
    exact ENNReal.ofReal_le_one.mpr (min_le_right _ _)
  · have positiveN : 0 < n := Nat.pos_of_ne_zero zero
    have compare : ENNReal.ofReal (A * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) ≤
        ENNReal.ofReal (Hl * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_nonneg _))
    apply compare.trans
    let U := {x | ∀ j < n, dist (T^[j] x) (T^[j] z) ≤ 4 * ε}
    have closedU : IsClosed U := by
      have closed : IsClosed (⋂ j ∈ Finset.range n,
          {x | dist (T^[j] x) (T^[j] z) ≤ 4 * ε}) :=
        isClosed_iInter (fun j => isClosed_iInter (fun _ =>
          isClosed_le ((T.continuous.iterate j).dist continuous_const) continuous_const))
      convert closed using 1
      ext x
      simp only [U, mem_ofPred_eq, mem_iInter, Finset.mem_range]
    apply CesaroProbability.cylinder_lower_bound_of_limit T T.continuous.measurable σ ν ι mono weak
      n gap (Hl * Real.exp (orbitSum T φ n z - (n : ℝ) * P)) (by positivity) U closedU
    intro N j hj left right
    have mass := lower N n positiveN z U closedU.measurableSet
      (fun x near i hi => (near i hi).le) j hj left right
    have realBound := ENNReal.toReal_mono (by finiteness) mass
    rw [ENNReal.toReal_ofReal (mul_nonneg positiveHl.le (Real.exp_nonneg _))] at realBound
    exact realBound

end LeanShared.ThermodynamicDefinitions
