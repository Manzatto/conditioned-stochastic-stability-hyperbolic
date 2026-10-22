module

public import LeanShared.Dynamics.PressureOrder
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-! A finite exponential count of separated orbit sets bounds the literal
weighted separated-set pressure. Padding the orbit horizon costs no entropy. -/
public noncomputable section
open Set Function Filter
open scoped Topology BigOperators ENNReal
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] {T : X → X} {φ : X → ℝ}

theorem partitionSum_bound_of_card (B : ℝ) (potential : ∀ x, φ x ≤ B)
    (a n p : ℕ) (ε : ℝ)
    (count : ∀ s : Finset X, Separated T univ n ε s → s.card ≤ a^(n+p)) :
    separatedPartitionSum T φ univ n ε ≤ (a : ℝ≥0∞)^(n+p)*ENNReal.ofReal (Real.exp ((n : ℝ)*B)) := by
  classical
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun hs => ?_
  calc
    _ ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp ((n : ℝ)*B)) := by
      apply Finset.sum_le_sum
      intro x _
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc
        orbitSum T φ n x ≤ ∑ _j ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun j _ => potential _)
        _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    _ = (s.card : ℝ≥0∞)*ENNReal.ofReal (Real.exp ((n : ℝ)*B)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul' (by exact_mod_cast count s hs) le_rfl

theorem pressure_le_of_card_bound (B : ℝ) (potential : ∀ x, φ x ≤ B)
    (a : ℕ) (positive : 0 < a)
    (counts : ∀ ε : ℝ, 0 < ε → ∃ p : ℕ, ∀ n : ℕ, ∀ s : Finset X,
      Separated T univ n ε s → s.card ≤ a^(n+p)) :
    pressure T φ univ ≤ (Real.log (a : ℝ)+B : ℝ) := by
  unfold pressure
  apply iSup_le
  intro ε
  obtain ⟨p,count⟩ := counts ε.val ε.property
  let upper : ℕ → ℝ := fun n => (1+(p : ℝ)*(n : ℝ)⁻¹)*Real.log (a : ℝ)+B
  have upperLimit : Tendsto upper atTop (𝓝 (Real.log (a : ℝ)+B)) := by
    have inverse : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    simpa only [upper,mul_zero,add_zero,one_mul] using
      ((inverse.const_mul (p : ℝ)).const_add 1).mul_const (Real.log (a : ℝ)) |>.add_const B
  have comparison : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T φ univ n ε.val).log ≤ (upper n : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have npos : (0 : ℝ) < n := by exact_mod_cast hn
    have apos : (0 : ℝ) < a := by exact_mod_cast positive
    have loga : (a : ℝ≥0∞).log=(Real.log (a : ℝ) : EReal) := by
      rw [←ENNReal.ofReal_natCast,ENNReal.log_ofReal_of_pos apos]
    have h := ENNReal.log_le_log (partitionSum_bound_of_card B potential a n p ε.val (count n))
    rw [ENNReal.log_mul_add,ENNReal.log_pow,loga,
      ENNReal.log_ofReal_of_pos (Real.exp_pos _),Real.log_exp] at h
    have factor : (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (inv_nonneg.mpr npos.le)
    have hmul := mul_le_mul_of_nonneg_left h factor
    have identity : (((n : ℝ)⁻¹ : ℝ) : EReal)*
        ((n+p : ℕ)*(Real.log (a : ℝ) : EReal)+((n : ℝ)*B : ℝ))=(upper n : EReal) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top factor (EReal.coe_ne_top _)]
      simp only [←EReal.coe_natCast,←EReal.coe_mul,←EReal.coe_add]
      congr 1
      dsimp [upper]
      push_cast
      field_simp
    exact hmul.trans_eq identity
  exact (limsup_le_limsup comparison).trans_eq
    ((continuous_coe_real_ereal.tendsto _).comp upperLimit).limsup_eq

end LeanShared.ThermodynamicDefinitions
