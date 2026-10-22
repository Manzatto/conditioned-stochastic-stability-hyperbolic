module

public import LeanShared.Dynamics.ProvedPressurePartitionEnvelope
public import LeanShared.Dynamics.ExpansivePeriodicSeparation

/-! Actual pressure controls every finite periodic weighted sum in a
compact expansive system.  The coefficient, exponent, exceptional finite
prefix and separated-set comparison are all produced internally.
-/

public noncomputable section
open Set Function MeasureTheory
open scoped BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem actual_periodic_weight_growth (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X →ᵇ ℝ) :
    ∃ P : ℝ, pressure T φ univ = (P : EReal) ∧ ∀ η : ℝ, 0 < η →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ s : Finset X,
        (∀ x ∈ s, (T : X → X)^[n] x = x) →
        (∑ x ∈ s, Real.exp (orbitSum T φ n x)) ≤ C * Real.exp (P + η) ^ n := by
  obtain ⟨P, pressureP, envelope⟩ := actual_pressure_log_envelope T c positiveC expansive φ
  obtain ⟨a, _positiveA, counts⟩ := FiniteExpansiveWords.exists_uniform_card_bound T c positiveC expansive
  obtain ⟨p, count⟩ := counts c positiveC
  have finite (n : ℕ) := partitionSum_positive_finite_of_count T φ n p a c (count n)
  refine ⟨P, pressureP, ?_⟩
  intro η positiveη
  obtain ⟨A, logarithm⟩ := envelope c positiveC η positiveη
  refine ⟨Real.exp A, Real.exp_pos A, ?_⟩
  intro n positiveN s fixed
  have separated := ExpansivePeriodicSeparation.separated T univ c
    (fun x _ y _ => expansive x y) n positiveN s (fun _ _ => mem_univ _) fixed
  have bound : ENNReal.ofReal (∑ x ∈ s, Real.exp (orbitSum T φ n x)) ≤
      separatedPartitionSum T φ univ n c := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
    exact le_iSup_of_le s (le_iSup_of_le separated le_rfl)
  have realBound := ENNReal.toReal_mono (finite n).2 bound
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))] at realBound
  calc
    _ ≤ (separatedPartitionSum T φ univ n c).toReal := realBound
    _ = Real.exp (Real.log (separatedPartitionSum T φ univ n c).toReal) :=
      (Real.exp_log (ENNReal.toReal_pos (finite n).1 (finite n).2)).symm
    _ ≤ Real.exp ((n : ℝ) * (P + η) + A) := Real.exp_le_exp.mpr (logarithm n)
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]; ring

end LeanShared.ThermodynamicDefinitions
