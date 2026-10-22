module
public import LeanShared.Dynamics.FiniteObservationInformationBound
public import LeanShared.Dynamics.ObservationPartitionEntropy
public import LeanShared.Dynamics.InvariantOrbitEnergy
public import LeanShared.Dynamics.PartitionEntropyRate

/-! The actual upper Gibbs bound forces the reverse entropy-energy
inequality. Finite word atoms lie in open Bowen cylinders; null atoms and
their logarithms are handled by the proved information inequality. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {a : ℕ}

omit [MeasurableSpace X] [BorelSpace X] in
private theorem open_cylinder (T : X → X) (continuous : Continuous T)
    (n : ℕ) (z : X) (ε : ℝ) :
    IsOpen {x | ∀ j < n, dist (T^[j] x) (T^[j] z) < ε} := by
  have opened := isOpen_biInter_finset (s := Finset.range n)
    (f := fun j => {x | dist (T^[j] x) (T^[j] z) < ε})
    (fun j _ => isOpen_lt ((continuous.iterate j).dist continuous_const) continuous_const)
  convert opened using 1
  ext x
  simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range]

theorem MeasurablePartition.finite_entropy_energy_of_upper_gibbs
    (Q : MeasurablePartition (X := X) a) (T : X → X) (continuous : Continuous T)
    (ν : ProbabilityMeasure X) (invariant : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (φ : X →ᵇ ℝ) (ε H P : ℝ) (positiveH : 0 < H)
    (mesh : ∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i → dist x y < ε)
    (gibbs : ∀ n z U, IsOpen U →
      (∀ x ∈ U, ∀ j < n, dist (T^[j] x) (T^[j] z) < ε) →
      (ν : Measure X) U ≤ ENNReal.ofReal (H * Real.exp (orbitSum T φ n z - (n : ℝ) * P)))
    (n : ℕ) :
    (n : ℝ) * P - Real.log H ≤ dynamicalEntropy Q T (ν : Measure X) n +
      (n : ℝ) * ∫ x, φ x ∂(ν : Measure X) := by
  let g := Q.wordObservation T n
  have upper (x : X) : (ν : Measure X).real (g ⁻¹' {g x}) ≤
      Real.exp (orbitSum T φ n x - ((n : ℝ) * P - Real.log H)) := by
    let U := {y | ∀ j < n, dist (T^[j] y) (T^[j] x) < ε}
    have contained : g ⁻¹' {g x} ⊆ U := by
      intro y hy j hj
      have equal : g y = g x := hy
      have labels := congrFun equal ⟨j, hj⟩
      have memberY := Q.label_mem (T^[j] y)
      change Q.label (T^[j] y) = Q.label (T^[j] x) at labels
      rw [labels] at memberY
      exact mesh _ _ _ memberY (Q.label_mem (T^[j] x))
    have mass := (measure_mono contained).trans
      (gibbs n x U (open_cylinder T continuous n x ε) (fun _ hx => hx))
    have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top mass
    rw [ENNReal.toReal_ofReal (mul_nonneg positiveH.le (Real.exp_nonneg _))] at realBound
    have exponential : Real.exp (orbitSum T φ n x - ((n : ℝ) * P - Real.log H)) =
        H * Real.exp (orbitSum T φ n x - (n : ℝ) * P) := by
      rw [show orbitSum T φ n x - ((n : ℝ) * P - Real.log H) =
        Real.log H + (orbitSum T φ n x - (n : ℝ) * P) by ring,
        Real.exp_add, Real.exp_log positiveH]
    exact realBound.trans_eq exponential.symm
  have bound := FiniteObservationEntropy.information_lower_bound (ν : Measure X) g
    (Q.wordObservation_measurable T continuous.measurable n) (orbitSum T φ n)
    (integrable_orbitSum T continuous (ν : Measure X) φ n) ((n : ℝ) * P - Real.log H) upper
  rw [Q.wordObservation_entropy T (ν : Measure X) n,
    integral_orbitSum_invariant T (ν : Measure X) invariant φ n] at bound
  exact bound

theorem MeasurablePartition.free_energy_ge_of_upper_gibbs
    (Q : MeasurablePartition (X := X) a) (T : X → X) (continuous : Continuous T)
    (ν : ProbabilityMeasure X) (invariant : MeasurePreserving T (ν : Measure X) (ν : Measure X))
    (φ : X →ᵇ ℝ) (ε H P : ℝ) (positiveH : 0 < H)
    (mesh : ∀ i x y, x ∈ Q.atom i → y ∈ Q.atom i → dist x y < ε)
    (gibbs : ∀ n z U, IsOpen U →
      (∀ x ∈ U, ∀ j < n, dist (T^[j] x) (T^[j] z) < ε) →
      (ν : Measure X) U ≤ ENNReal.ofReal (H * Real.exp (orbitSum T φ n z - (n : ℝ) * P))) :
    P ≤ Q.entropyRate T (ν : Measure X) + ∫ x, φ x ∂(ν : Measure X) := by
  have lower : ∀ᶠ n : ℕ in atTop, P - Real.log H / (n : ℝ) ≤
      dynamicalEntropy Q T (ν : Measure X) n / n + ∫ x, φ x ∂(ν : Measure X) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have positiveN : 0 < (n : ℝ) := by exact_mod_cast hn
    have bound := (div_le_div_of_nonneg_right
      (Q.finite_entropy_energy_of_upper_gibbs T continuous ν invariant φ ε H P positiveH mesh gibbs n)
      positiveN.le)
    simpa only [sub_div, add_div, mul_div_cancel_left₀ _ positiveN.ne',
      mul_div_cancel_left₀ _ positiveN.ne'] using bound
  have vanishes : Tendsto (fun n : ℕ => Real.log H / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_div, mul_zero, one_mul] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log H)
  have leftLimit : Tendsto (fun n : ℕ => P - Real.log H / (n : ℝ)) atTop (𝓝 P) := by
    simpa only [sub_zero] using vanishes.const_sub P
  exact le_of_tendsto_of_tendsto leftLimit
    ((Q.entropyRate_tendsto T (ν : Measure X) invariant).add_const _) lower

end LeanShared.ThermodynamicDefinitions
