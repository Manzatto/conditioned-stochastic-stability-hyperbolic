module

public import LeanShared.Dynamics.CesaroProbability
public import LeanShared.Dynamics.FiniteProbabilityMixture
public import LeanShared.Dynamics.ObservationPartitionEntropy

/-! Concavity of actual dynamical partition entropy under actual Cesaro
averaging of the initial probability. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators ENNReal
namespace LeanShared.CesaroProbability
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
theorem measure_eq_mixture (T : X → X) (μ : ProbabilityMeasure X) (n : ℕ) :
    measure T μ n = FiniteProbabilityMixture.measure
      (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹) (fun j => μ.map (T^[j.val])) := by
  have coefficient : ENNReal.ofReal ((n+1 : ℝ)⁻¹)=((n+1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity)]
    congr 1
    simpa only [Nat.cast_add,Nat.cast_one] using ENNReal.ofReal_natCast (n+1)
  simp only [measure,FiniteProbabilityMixture.measure,coefficient,ProbabilityMeasure.toMeasure_map,
    ←Finset.smul_sum]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun j => (μ : Measure X).map (T^[j])) (n+1)).symm

omit [MetricSpace X] [BorelSpace X] in
theorem dynamicalEntropy_concavity {k : ℕ}
    (P : ThermodynamicDefinitions.MeasurablePartition (X := X) k)
    (T : X → X) (μ : ProbabilityMeasure X) (n m : ℕ) :
    (n+1 : ℝ)⁻¹ * ∑ j : Fin (n+1),
      ThermodynamicDefinitions.dynamicalEntropy P T ((μ.map (T^[j.val])) : Measure X) m ≤
      ThermodynamicDefinitions.dynamicalEntropy P T (measure T μ n) m := by
  have nonnegative : ∀ _j : Fin (n+1), 0 ≤ (n+1 : ℝ)⁻¹ := fun _ => by positivity
  have total : ∑ _j : Fin (n+1), (n+1 : ℝ)⁻¹=1 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    simpa only [Nat.cast_add,Nat.cast_one] using
      mul_inv_cancel₀ (show (n+1 : ℝ) ≠ 0 by positivity)
  have bound := FiniteProbabilityMixture.observation_entropy_concave
    (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹) (fun j => μ.map (T^[j.val])) nonnegative total
    (P.wordObservation T m)
  rw [←measure_eq_mixture] at bound
  simpa only [P.wordObservation_entropy,←Finset.mul_sum] using bound

end LeanShared.CesaroProbability
