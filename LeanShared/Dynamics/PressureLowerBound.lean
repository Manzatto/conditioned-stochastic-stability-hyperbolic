module

public import LeanShared.Dynamics.PressureOrder
import Mathlib.Tactic.FieldSimp

/-! A single surviving orbit provides the actual lower pressure bound. -/
public noncomputable section
open Set Function Filter
open scoped Topology BigOperators ENNReal
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [Nonempty X] {T : X → X} {φ : X → ℝ}

theorem pressure_ge_of_lower_bound (B : ℝ) (bound : ∀ x, B ≤ φ x) :
    (B : EReal) ≤ pressure T φ univ := by
  classical
  let x : X := Classical.arbitrary X
  have partitionLower (n : ℕ) (ε : ℝ) :
      ENNReal.ofReal (Real.exp ((n : ℝ)*B)) ≤ separatedPartitionSum T φ univ n ε := by
    have separated : Separated T univ n ε {x} := by
      constructor
      · exact fun _ _ => mem_univ _
      · intro y hy z hz different
        have ey : y=x := Finset.mem_singleton.mp hy
        have ez : z=x := Finset.mem_singleton.mp hz
        exact (different (ey.trans ez.symm)).elim
    have orbitLower : (n : ℝ)*B ≤ orbitSum T φ n x := by
      calc
        _ = ∑ _j ∈ Finset.range n, B := by
          simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun j _ => bound _)
    calc
      _ ≤ ENNReal.ofReal (Real.exp (orbitSum T φ n x)) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr orbitLower)
      _ = ∑ y ∈ ({x} : Finset X), ENNReal.ofReal (Real.exp (orbitSum T φ n y)) := by
        simp only [Finset.sum_singleton]
      _ ≤ _ := le_iSup_of_le {x} (by simp only [iSup_pos separated]; exact le_rfl)
  have normalized : ∀ᶠ n : ℕ in atTop, (B : EReal) ≤
      (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T φ univ n 1).log := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have positive : (0 : ℝ) < n := by exact_mod_cast hn
    have h := ENNReal.log_le_log (partitionLower n 1)
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _),Real.log_exp] at h
    have mult := mul_le_mul_of_nonneg_left h
      (EReal.coe_nonneg.mpr (inv_nonneg.mpr positive.le))
    have identity : (((n : ℝ)⁻¹ : ℝ) : EReal)*((n : ℝ)*B : ℝ)=(B : EReal) := by
      rw [←EReal.coe_mul]
      congr 1
      field_simp
    rwa [identity] at mult
  have lower := limsup_le_limsup normalized
  simp only [limsup_const] at lower
  exact lower.trans (le_iSup (fun ε : {ε : ℝ // 0 < ε} =>
    limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*
      (separatedPartitionSum T φ univ n ε.val).log) atTop) ⟨1,zero_lt_one⟩)

end LeanShared.ThermodynamicDefinitions
