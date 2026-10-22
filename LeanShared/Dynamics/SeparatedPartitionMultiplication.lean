module

public import LeanShared.Dynamics.SeparatedPartitionApproximation
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Finite weighted gluing and uniform scale comparison imply a genuine
shifted product bound for the literal separated partition suprema. Finite
sets approximating both suprema are constructed internally. -/
public noncomputable section
open Set
open scoped BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

set_option maxHeartbeats 1600000 in
theorem partition_multiplication_of_gluing (T : X → X) (φ : X → ℝ)
    (K : Set X) (ρ ε c C : ℝ) (positiveC : 0 < C) (nonnegativeC : 0 ≤ c) (gap : ℕ)
    (nonzero : ∀ n, separatedPartitionSum T φ K n ρ ≠ 0)
    (finite : ∀ n, separatedPartitionSum T φ K n ρ ≠ ⊤)
    (comparison : ∀ n, separatedPartitionSum T φ K n ε ≤
      ENNReal.ofReal C * separatedPartitionSum T φ K n ρ)
    (gluing : ∀ n, 0 < n → ∀ m, 0 < m → ∀ s t : Finset X,
      Separated T K n ρ s → Separated T K m ρ t →
      ∃ q : Finset X, Separated T K (n + m + gap) ε q ∧
        c * (∑ x ∈ s, Real.exp (orbitSum T φ n x)) *
          (∑ y ∈ t, Real.exp (orbitSum T φ m y)) ≤
            ∑ z ∈ q, Real.exp (orbitSum T φ (n + m + gap) z)) :
    ∀ n, 0 < n → ∀ m, 0 < m →
      (c / (4 * C)) * (separatedPartitionSum T φ K n ρ).toReal *
        (separatedPartitionSum T φ K m ρ).toReal ≤
          (separatedPartitionSum T φ K (n + m + gap) ρ).toReal := by
  classical
  intro n hn m hm
  obtain ⟨s, _, separatedS, lowerS, _⟩ := exists_separated_half_sum T φ K n ρ (nonzero n) (finite n)
  obtain ⟨t, _, separatedT, lowerT, _⟩ := exists_separated_half_sum T φ K m ρ (nonzero m) (finite m)
  obtain ⟨q, separatedQ, productBound⟩ := gluing n hn m hm s t separatedS separatedT
  have lower := mul_le_mul lowerS.le lowerT.le
    (div_nonneg ENNReal.toReal_nonneg (by norm_num))
    (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _))
  have weighted := mul_le_mul_of_nonneg_left lower nonnegativeC
  have upperENN : ENNReal.ofReal (∑ z ∈ q, Real.exp (orbitSum T φ (n + m + gap) z)) ≤
      ENNReal.ofReal C * separatedPartitionSum T φ K (n + m + gap) ρ := by
    apply le_trans _ (comparison _)
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.exp_nonneg _)]
    unfold separatedPartitionSum
    exact le_iSup_of_le q (le_iSup_of_le separatedQ le_rfl)
  have upper := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (finite _)) upperENN
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg (fun _ _ => Real.exp_nonneg _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal positiveC.le] at upper
  have combined : c * ((separatedPartitionSum T φ K n ρ).toReal / 2) *
      ((separatedPartitionSum T φ K m ρ).toReal / 2) ≤
        C * (separatedPartitionSum T φ K (n + m + gap) ρ).toReal := by
    calc
      _ ≤ c * (∑ x ∈ s, Real.exp (orbitSum T φ n x)) *
          (∑ y ∈ t, Real.exp (orbitSum T φ m y)) := by
        simpa only [mul_assoc] using weighted
      _ ≤ _ := productBound.trans upper
  calc
    _ = (c * ((separatedPartitionSum T φ K n ρ).toReal / 2) *
        ((separatedPartitionSum T φ K m ρ).toReal / 2)) / C := by field_simp; ring
    _ ≤ _ := (div_le_iff₀ positiveC).mpr (by simpa only [mul_comm] using combined)

end LeanShared.ThermodynamicDefinitions
