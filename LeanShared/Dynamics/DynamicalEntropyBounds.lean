module

public import LeanShared.Dynamics.DynamicalPartition
public import LeanShared.Dynamics.FiniteEntropyBounds
public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.FieldSimp

/-! Literal finite-time partition entropy has the exact uniform alphabet
bound; each partition's asymptotic entropy rate is therefore finite. -/
public noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MeasurableSpace X] {k : ℕ}

private theorem nonempty_index [Nonempty X] (P : MeasurablePartition (X := X) k) :
    Nonempty (Fin k) := by
  let x : X := Classical.arbitrary X
  have member : x ∈ ⋃ i, P.atom i := by rw [P.covering]; exact mem_univ _
  obtain ⟨i,_⟩ := mem_iUnion.mp member
  exact ⟨i⟩

/-- The bound counts exactly k^n dynamical atoms, including zero atoms. -/
theorem MeasurablePartition.dynamicalEntropy_bounds (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) : 0 ≤ dynamicalEntropy P T μ n ∧ dynamicalEntropy P T μ n ≤ (n : ℝ)*Real.log (k : ℝ) := by
  let : Nonempty X := nonempty_of_isProbabilityMeasure μ
  let : Nonempty (Fin k) := nonempty_index P
  have bounds := FiniteEntropyBounds.bounds (fun w : Fin n → Fin k => μ.real (dynamicalAtom P T n w))
    (fun _ => measureReal_nonneg) (P.dynamicalAtoms_total T measurable μ n)
  simpa only [dynamicalEntropy,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] using bounds

/-- No limiting partition-entropy scalar is assumed: its actual liminf is
between zero and log k, and hence cannot be an extended infinity. -/
theorem MeasurablePartition.entropy_rate_bounds (P : MeasurablePartition (X := X) k)
    (T : X → X) (measurable : Measurable T) (μ : Measure X) [IsProbabilityMeasure μ] :
    (0 : EReal) ≤ liminf (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal)) atTop ∧
    liminf (fun n : ℕ => (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal)) atTop ≤
      (Real.log (k : ℝ) : EReal) := by
  have lower : ∀ᶠ n : ℕ in atTop, (0 : EReal) ≤
      (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal) := by
    exact Eventually.of_forall (fun n => EReal.coe_nonneg.mpr
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (P.dynamicalEntropy_bounds T measurable μ n).1))
  have upper : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ)⁻¹*dynamicalEntropy P T μ n : ℝ) : EReal) ≤ (Real.log (k : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have positive : (0 : ℝ) < n := by exact_mod_cast hn
    apply EReal.coe_le_coe_iff.mpr
    calc
      _ ≤ (n : ℝ)⁻¹*((n : ℝ)*Real.log (k : ℝ)) :=
        mul_le_mul_of_nonneg_left (P.dynamicalEntropy_bounds T measurable μ n).2
          (inv_nonneg.mpr positive.le)
      _ = _ := by field_simp
  exact ⟨by simpa only [liminf_const] using liminf_le_liminf lower,
    by simpa only [liminf_const] using liminf_le_liminf upper⟩

end LeanShared.ThermodynamicDefinitions
