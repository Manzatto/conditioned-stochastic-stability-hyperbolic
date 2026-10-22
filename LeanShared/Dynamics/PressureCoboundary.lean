module

public import LeanShared.Dynamics.PressureBoundedPerturbation

/-! Adding an actual bounded coboundary preserves literal weighted
separated-set pressure, including infinite pressure values. -/
public noncomputable section
open Set Function Filter
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] {T : X → X} {K : Set X} {φ ψ u : X → ℝ}

omit [MetricSpace X] in
theorem orbitSum_coboundary (invariant : MapsTo T K K)
    (same : ∀ x ∈ K, φ x=ψ x+u x-u (T x)) (n : ℕ) {x : X} (hx : x ∈ K) :
    orbitSum T φ n x=orbitSum T ψ n x+u x-u (T^[n] x) := by
  have terms (j : ℕ) : φ (T^[j] x)=ψ (T^[j] x)+(u (T^[j] x)-u (T^[j+1] x)) := by
    rw [same _ (invariant.iterate j hx),iterate_succ_apply']
    ring
  have sum := Finset.sum_congr (s₁ := Finset.range n) rfl (fun j _ => terms j)
  change orbitSum T φ n x = _ at sum
  rw [Finset.sum_add_distrib] at sum
  have telescope := congrArg Neg.neg (Finset.sum_range_sub (fun j => u (T^[j] x)) n)
  rw [←Finset.sum_neg_distrib] at telescope
  simp only [neg_sub,iterate_zero_apply] at telescope
  rw [telescope] at sum
  simpa only [iterate_zero_apply,orbitSum,add_sub_assoc] using sum

private theorem pressure_le_of_orbit_bound (C : ℝ)
    (bound : ∀ n x, x ∈ K → orbitSum T φ n x ≤ orbitSum T ψ n x+C) :
    pressure T φ K ≤ pressure T ψ K := by
  classical
  have partition (n : ℕ) (ε : ℝ) : separatedPartitionSum T φ K n ε ≤
      ENNReal.ofReal (Real.exp C)*separatedPartitionSum T ψ K n ε := by
    unfold separatedPartitionSum
    refine iSup_le fun s => iSup_le fun hs => ?_
    calc
      _ ≤ ∑ x ∈ s, ENNReal.ofReal (Real.exp C)*ENNReal.ofReal (Real.exp (orbitSum T ψ n x)) := by
        apply Finset.sum_le_sum
        intro x hx
        have h := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (bound n x (hs.1 x hx)))
        rw [Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)] at h
        simpa only [mul_comm] using h
      _ = ENNReal.ofReal (Real.exp C)*∑ x ∈ s, ENNReal.ofReal (Real.exp (orbitSum T ψ n x)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul' le_rfl (le_iSup_of_le s (by simp only [iSup_pos hs]; exact le_rfl))
  unfold pressure
  apply iSup_le
  intro ε
  have compare : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T φ K n ε.val).log ≤
      (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T ψ K n ε.val).log+
        (((n : ℝ)⁻¹*C : ℝ) : EReal) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have logs := ENNReal.log_le_log (partition n ε.val)
    rw [ENNReal.log_mul_add,ENNReal.log_ofReal_of_pos (Real.exp_pos _),Real.log_exp] at logs
    have factor : (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.mpr (by positivity)
    have scaled := mul_le_mul_of_nonneg_left logs factor
    rw [EReal.left_distrib_of_nonneg_of_ne_top factor (EReal.coe_ne_top _),←EReal.coe_mul] at scaled
    simpa only [add_comm] using scaled
  have error := continuous_coe_real_ereal.continuousAt.tendsto.comp
    (tendsto_inv_atTop_nhds_zero_nat.mul_const C)
  simp only [Function.comp_def,zero_mul,EReal.coe_zero] at error
  have addition := EReal.limsup_add_le (f := atTop)
    (u := fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*(separatedPartitionSum T ψ K n ε.val).log)
    (v := fun n : ℕ => (((n : ℝ)⁻¹*C : ℝ) : EReal))
    (Or.inr (by rw [error.limsup_eq]; exact EReal.zero_ne_top))
    (Or.inr (by rw [error.limsup_eq]; exact EReal.zero_ne_bot))
  rw [error.limsup_eq,add_zero] at addition
  exact (limsup_le_limsup compare).trans (addition.trans (le_iSup
    (fun e : {e : ℝ // 0 < e} => limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal)*
      (separatedPartitionSum T ψ K n e.val).log) atTop) ε))

theorem pressure_coboundary (invariant : MapsTo T K K) (B : ℝ)
    (bounded : ∀ x ∈ K, |u x| ≤ B)
    (same : ∀ x ∈ K, φ x=ψ x+u x-u (T x)) : pressure T φ K=pressure T ψ K := by
  apply le_antisymm
  · apply pressure_le_of_orbit_bound (2*B)
    intro n x hx
    rw [orbitSum_coboundary invariant same n hx]
    have first := (abs_le.mp (bounded x hx)).2
    have second := (abs_le.mp (bounded _ (invariant.iterate n hx))).1
    linarith
  · apply pressure_le_of_orbit_bound (2*B)
    intro n x hx
    have equal := orbitSum_coboundary invariant same n hx
    have first := (abs_le.mp (bounded x hx)).1
    have second := (abs_le.mp (bounded _ (invariant.iterate n hx))).2
    linarith

end LeanShared.ThermodynamicDefinitions
