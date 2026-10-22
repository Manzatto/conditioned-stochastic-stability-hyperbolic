module

public import LeanShared.Dynamics.SeparatedGibbsBlockEstimate

/-! Uniform scalar bounds on actual separated Gibbs log partition sums,
derived from the potential norm and a finite alphabet count. -/
public noncomputable section
open Set Function MeasureTheory
open scoped BigOperators BoundedContinuousFunction
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X]

theorem normalized_gibbs_sum_bounds (T : X → X) (φ : X →ᵇ ℝ)
    (n : ℕ) (s : Finset X) (nonempty : s.Nonempty)
    (a : ℕ) (positive : 0 < a) (p : ℕ)
    (count : s.card ≤ a^((n+1)*(p+1))) :
    -‖φ‖ ≤ Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ) ∧
      Real.log (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x))/(n+1 : ℝ) ≤
        (p+1 : ℝ)*Real.log (a : ℝ)+‖φ‖ := by
  classical
  have npos : (0 : ℝ) < n+1 := by positivity
  have apos : (0 : ℝ) < a := by exact_mod_cast positive
  have sumpos : 0 < ∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x) :=
    Finset.sum_pos (fun x _ => Real.exp_pos _) nonempty
  have orbit (x : X) : -(n+1 : ℝ)*‖φ‖ ≤ orbitSum T φ (n+1) x ∧
      orbitSum T φ (n+1) x ≤ (n+1 : ℝ)*‖φ‖ := by
    have bounds (j : ℕ) : -‖φ‖ ≤ φ (T^[j] x) ∧ φ (T^[j] x) ≤ ‖φ‖ := by
      exact abs_le.mp (φ.norm_coe_le_norm _)
    constructor
    · have h := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j _ => (bounds j).1)
      simpa only [orbitSum,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_neg,neg_mul] using h
    · have h := Finset.sum_le_sum (s := Finset.range (n+1)) (fun j _ => (bounds j).2)
      simpa only [orbitSum,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one] using h
  constructor
  · obtain ⟨x,hx⟩ := nonempty
    have one := Finset.single_le_sum (fun y _ => (Real.exp_pos (orbitSum T φ (n+1) y)).le) hx
    have h := (Real.log_le_log (Real.exp_pos _) one)
    rw [Real.log_exp] at h
    exact (le_div_iff₀ npos).mpr (by nlinarith [(orbit x).1])
  · have sumBound : (∑ x ∈ s, Real.exp (orbitSum T φ (n+1) x)) ≤
        (a : ℝ)^((n+1)*(p+1))*Real.exp ((n+1 : ℝ)*‖φ‖) := by
      calc
        _ ≤ ∑ _x ∈ s, Real.exp ((n+1 : ℝ)*‖φ‖) :=
          Finset.sum_le_sum (fun x _ => Real.exp_le_exp.mpr (orbit x).2)
        _ = (s.card : ℝ)*Real.exp ((n+1 : ℝ)*‖φ‖) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast count) (Real.exp_pos _).le
    have h := Real.log_le_log sumpos sumBound
    rw [Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)), Real.log_pow,Real.log_exp] at h
    apply (div_le_iff₀ npos).mpr
    push_cast at h
    nlinarith

end LeanShared.ThermodynamicDefinitions
