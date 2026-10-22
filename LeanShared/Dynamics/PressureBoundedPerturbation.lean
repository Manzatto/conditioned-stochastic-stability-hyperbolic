module

public import LeanShared.Dynamics.PressureOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Literal pressure is stable under bounded changes of potential on the
invariant set. In particular finiteness and real pressure scalars for positive
envelopes are derived from one finite reference pressure. -/
public noncomputable section
open Set Filter
open scoped Topology BigOperators ENNReal
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X} {φ ψ : X → ℝ}

theorem pressure_le_add (invariant : MapsTo T K K) (c : ℝ)
    (bound : ∀ x ∈ K, φ x ≤ ψ x+c) :
    pressure T φ K ≤ pressure T ψ K+(c : EReal) := by
  have normalized (ε : ℝ) : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T φ K n ε).log ≤
      (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T ψ K n ε).log+(c : EReal) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have positive : (0 : ℝ) < n := by exact_mod_cast hn
    have factor : (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) :=
      EReal.coe_nonneg.mpr (inv_nonneg.mpr positive.le)
    have logbound := ENNReal.log_le_log (separatedPartitionSum_le_mul invariant c bound n ε)
    rw [ENNReal.log_mul_add,ENNReal.log_ofReal_of_pos (Real.exp_pos _),Real.log_exp] at logbound
    have result := mul_le_mul_of_nonneg_left logbound factor
    rw [EReal.left_distrib_of_nonneg_of_ne_top factor (EReal.coe_ne_top _)] at result
    have scalar : (((n : ℝ)⁻¹ : ℝ) : EReal)*((n : ℝ)*c : ℝ)= (c : EReal) := by
      rw [←EReal.coe_mul]
      congr 1
      field_simp
    rw [scalar] at result
    simpa only [add_comm] using result
  unfold pressure
  apply iSup_le
  intro ε
  have mono := limsup_le_limsup (normalized ε.val)
  have addition := EReal.limsup_add_le (f := atTop)
    (u := fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T ψ K n ε.val).log)
    (v := fun _ : ℕ => (c : EReal)) (Or.inr (by simp)) (Or.inr (by simp))
  simp only [limsup_const] at addition
  exact mono.trans (addition.trans (add_le_add (le_iSup (fun ε : {ε : ℝ // 0 < ε} =>
    limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*
      (separatedPartitionSum T ψ K n ε.val).log) atTop) ε) le_rfl))

/-- A bounded change on the invariant core constructs a finite real pressure;
its finiteness is not a separate source assumption. -/
theorem finite_pressure_of_bounded_difference (invariant : MapsTo T K K)
    (P c : ℝ) (finite : pressure T ψ K = (P : EReal))
    (upper : ∀ x ∈ K, φ x ≤ ψ x+c) (lower : ∀ x ∈ K, ψ x ≤ φ x+c) :
    ∃ Q : ℝ, pressure T φ K=(Q : EReal) ∧ P-c ≤ Q ∧ Q ≤ P+c := by
  have up := pressure_le_add invariant c upper
  have down := pressure_le_add invariant c lower
  rw [finite,←EReal.coe_add] at up
  rw [finite] at down
  have nottop : pressure T φ K ≠ ⊤ := by
    intro ht
    rw [ht] at up
    exact EReal.coe_ne_top (P+c) (top_le_iff.mp up)
  have notbot : pressure T φ K ≠ ⊥ := by
    intro hb
    rw [hb] at down
    simp only [EReal.bot_add,le_bot_iff] at down
    exact EReal.coe_ne_bot P down
  let Q := (pressure T φ K).toReal
  have identity : pressure T φ K = (Q : EReal) := (EReal.coe_toReal nottop notbot).symm
  refine ⟨Q,identity,?_,?_⟩
  · rw [identity,←EReal.coe_add] at down
    have hh := EReal.coe_le_coe_iff.mp down
    linarith
  · rw [identity] at up
    exact EReal.coe_le_coe_iff.mp up

end LeanShared.ThermodynamicDefinitions
