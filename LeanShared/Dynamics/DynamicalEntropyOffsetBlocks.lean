module

public import LeanShared.Dynamics.DynamicalEntropyBlocks
public import LeanShared.Dynamics.OffsetBlockSum
import Mathlib.Tactic.Linarith

/-! The averaged-offset finite-time entropy estimate for arbitrary
initial probabilities, with a uniform O(m² log k) boundary cost. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}
namespace MeasurablePartition

private theorem log_card_nonnegative (P : MeasurablePartition (X := X) k)
    (μ : Measure X) [IsProbabilityMeasure μ] : 0 ≤ Real.log (k : ℝ) := by
  let x : X := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  have member : x ∈ ⋃ i, P.atom i := by rw [P.covering]; exact mem_univ x
  obtain ⟨i,_⟩ := mem_iUnion.mp member
  have index := i.is_lt
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ k by omega)

private theorem shifted_map (T : X → X) (measurable : Measurable T) (μ : Measure X) (r j : ℕ) :
    (μ.map (T^[r])).map (T^[j])=μ.map (T^[r+j]) := by
  rw [Measure.map_map (measurable.iterate j) (measurable.iterate r)]
  congr 1
  funext x
  rw [Nat.add_comm r j,iterate_add_apply]
  rfl

theorem dynamicalEntropy_offset_blocks_le (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (m n r : ℕ) (positive : 0 < m) (large : m ≤ n) (offset : r < m) :
    dynamicalEntropy P T μ n ≤
      (∑ j ∈ Finset.range ((n-r)/m), dynamicalEntropy P T (μ.map (T^[r+j*m])) m) +
      (2*m : ℝ)*Real.log (k : ℝ) := by
  have rle : r ≤ n := (Nat.le_of_lt offset).trans large
  have start := P.dynamicalEntropy_add_le T μ measurable r (n-r)
  rw [Nat.add_sub_of_le rle] at start
  have blocks := P.dynamicalEntropy_blocks_le T measurable (μ.map (T^[r])) m ((n-r)/m) ((n-r)%m)
  rw [Nat.mul_comm ((n-r)/m) m,Nat.div_add_mod] at blocks
  simp_rw [shifted_map T measurable μ] at blocks
  have first := (P.dynamicalEntropy_bounds T measurable μ r).2
  have remainder : (r : ℝ)+((n-r)%m : ℕ) ≤ 2*(m : ℝ) := by
    exact_mod_cast (show r+(n-r)%m ≤ 2*m by have := Nat.mod_lt (n-r) positive; omega)
  have tail := mul_le_mul_of_nonneg_right remainder (P.log_card_nonnegative μ)
  linarith

/-- The actual Misiurewicz block estimate: averaging over every residue
class pays only a fixed boundary cost and uses every start at most once. -/
theorem dynamicalEntropy_averaged_blocks_le (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (m n : ℕ) (positive : 0 < m) (large : m ≤ n) :
    (m : ℝ)*dynamicalEntropy P T μ n ≤
      (∑ j ∈ Finset.range n, dynamicalEntropy P T (μ.map (T^[j])) m) +
      2*(m : ℝ)*m*Real.log (k : ℝ) := by
  have sum := Finset.sum_le_sum (s := Finset.range m) (fun r hr =>
    P.dynamicalEntropy_offset_blocks_le T measurable μ m n r positive large (Finset.mem_range.mp hr))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum
  have cover := LeanShared.OffsetBlockSum.le_all_starts m n positive
    (fun j => dynamicalEntropy P T (μ.map (T^[j])) m)
    (fun j => (P.dynamicalEntropy_bounds T measurable (μ.map (T^[j])) m).1)
  calc
    _ ≤ _ := sum
    _ ≤ (∑ j ∈ Finset.range n, dynamicalEntropy P T (μ.map (T^[j])) m) +
        (m : ℝ)*((2*m : ℝ)*Real.log (k : ℝ)) := add_le_add cover le_rfl
    _ = _ := by ring

end MeasurablePartition
end LeanShared.ThermodynamicDefinitions
