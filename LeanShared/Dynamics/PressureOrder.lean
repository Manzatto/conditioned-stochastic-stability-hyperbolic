module

public import LeanShared.Dynamics.ThermodynamicDefinitions
public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Order of the literal separated-set pressure follows from finite Bowen
sums. It is not an additional thermodynamic source theorem. -/
public noncomputable section
open Set Filter
open scoped Topology BigOperators ENNReal
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X} {φ ψ : X → ℝ}

omit [MetricSpace X] in
theorem orbitSum_le_add_const (invariant : MapsTo T K K) (c : ℝ)
    (bound : ∀ x ∈ K, φ x ≤ ψ x+c) (n : ℕ) {x : X} (hx : x ∈ K) :
    orbitSum T φ n x ≤ orbitSum T ψ n x+(n : ℝ)*c := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, (ψ (T^[j] x)+c) :=
      Finset.sum_le_sum (fun j _ => bound _ (invariant.iterate j hx))
    _ = _ := by simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,
      nsmul_eq_mul,orbitSum]

theorem separatedPartitionSum_le_mul (invariant : MapsTo T K K) (c : ℝ)
    (bound : ∀ x ∈ K, φ x ≤ ψ x+c) (n : ℕ) (ε : ℝ) :
    separatedPartitionSum T φ K n ε ≤ ENNReal.ofReal (Real.exp ((n : ℝ)*c))*
      separatedPartitionSum T ψ K n ε := by
  classical
  unfold separatedPartitionSum
  refine iSup_le fun s => iSup_le fun hs => ?_
  calc
    _ ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp ((n : ℝ)*c))*
        ENNReal.ofReal (Real.exp (orbitSum T ψ n x)) := by
      apply Finset.sum_le_sum
      intro x hx
      have h := orbitSum_le_add_const invariant c bound n (hs.1 x hx)
      calc
        _ ≤ ENNReal.ofReal (Real.exp (orbitSum T ψ n x+(n : ℝ)*c)) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h)
        _ = _ := by rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]; ac_rfl
    _ = ENNReal.ofReal (Real.exp ((n : ℝ)*c))*
        ∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T ψ n x)) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul' le_rfl (le_iSup_of_le s (by simp only [iSup_pos hs]; exact le_rfl))

theorem pressure_order (invariant : MapsTo T K K) (c Pφ Pψ : ℝ)
    (first : pressure T φ K = (Pφ : EReal)) (second : pressure T ψ K = (Pψ : EReal))
    (bound : ∀ x ∈ K, φ x ≤ ψ x+c) : Pφ ≤ Pψ+c := by
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
  have comparison : pressure T φ K ≤ (Pψ+c : ℝ) := by
    unfold pressure
    apply iSup_le
    intro ε
    have mono := limsup_le_limsup (normalized ε.val)
    have add := EReal.limsup_add_le (f := atTop)
      (u := fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T ψ K n ε.val).log)
      (v := fun _ : ℕ => (c : EReal))
      (Or.inr (by simp)) (Or.inr (by simp))
    have upper : limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*
        (separatedPartitionSum T ψ K n ε.val).log) atTop ≤ (Pψ : EReal) := by
      rw [←second]
      exact le_iSup (fun ε : {ε : ℝ // 0 < ε} => limsup (fun n : ℕ =>
        (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T ψ K n ε.val).log) atTop) ε
    simp only [limsup_const] at add
    have total := mono.trans (add.trans (add_le_add upper (le_refl (c : EReal))))
    simpa only [Pi.add_apply,limsup_const,←EReal.coe_add] using total
  rw [first] at comparison
  exact EReal.coe_le_coe_iff.mp comparison

end LeanShared.ThermodynamicDefinitions
