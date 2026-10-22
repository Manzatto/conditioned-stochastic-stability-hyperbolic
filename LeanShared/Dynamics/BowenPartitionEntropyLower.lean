module

public import LeanShared.Dynamics.BlockGeneratorEntropy
public import LeanShared.Dynamics.ExpansiveEntropyIterate

/-! Every actual finite partition with n-step Bowen-small atoms has
one-observation Shannon entropy at least n times the full metric entropy.
The generator property and iterate entropy scaling are conclusions proved
from the original compact expansivity, not source assumptions. -/
public noncomputable section
open Set Function MeasureTheory
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem bowen_partition_entropy_lower {k : ℕ} (P : MeasurablePartition (X := X) k)
    (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) μ)
    (n : ℕ) (positive : 0 < n)
    (mesh : ∀ i x y, x ∈ P.atom i → y ∈ P.atom i →
      ∀ j < n, dist (T^[j] x) (T^[j] y) ≤ c) :
    (n : ℝ) * (entropy T (μ : Measure X)).toReal ≤
      dynamicalEntropy P (T^n : X ≃ₜ X) (μ : Measure X) 1 := by
  have generator := P.entropy_eq_block_generator_rate T c expansive n positive mesh μ
    (by simpa only [DiffeomorphismIterates.coe_pow] using invariant.iterate n)
  have iterate := entropy_iterate_of_expansive T c positiveC expansive μ invariant n positive
  have generator' : entropy ((T : X → X)^[n]) (μ : Measure X) =
      (P.entropyRate (T^n : X ≃ₜ X) (μ : Measure X) : EReal) := by
    simpa only [DiffeomorphismIterates.coe_pow] using generator
  have numeric : (n : ℝ) * (entropy T (μ : Measure X)).toReal =
      P.entropyRate (T^n : X ≃ₜ X) (μ : Measure X) := EReal.coe_injective (iterate.symm.trans generator')
  rw [numeric]
  simpa only [Nat.cast_one, div_one] using
    P.entropyRate_le_div (T^n : X ≃ₜ X) (T^n : X ≃ₜ X).continuous.measurable (μ : Measure X) 1 Nat.one_pos

end LeanShared.ThermodynamicDefinitions
