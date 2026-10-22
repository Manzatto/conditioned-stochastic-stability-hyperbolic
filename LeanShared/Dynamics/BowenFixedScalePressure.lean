module

public import LeanShared.Dynamics.BowenPartitionScaleComparison
public import LeanShared.Dynamics.PressureBoundedPerturbation

/-! On a compact expansive system with Bowen distortion, the literal
pressure is computed at any sufficiently small fixed scale. Uniform
partition comparison is proved internally; no limiting pressure source is
introduced. Infinite pressure values are included in the identity. -/
public noncomputable section
open Set Function Filter
open scoped Topology BigOperators
namespace LeanShared.ThermodynamicDefinitions
variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]

set_option maxHeartbeats 1600000 in
theorem pressure_at_bowen_scale (T : X ≃ₜ X) (c : ℝ) (positiveC : 0 < c)
    (expansive : ∀ x y, (∀ j : ℕ,
      dist ((T : X → X)^[j] x) ((T : X → X)^[j] y) ≤ c ∧
      dist ((T.symm : X → X)^[j] x) ((T.symm : X → X)^[j] y) ≤ c) → x = y)
    (φ : X → ℝ) (ρ D : ℝ) (positiveρ : 0 < ρ) (coarse : 2 * ρ ≤ c)
    (bowen : ∀ n x y, (∀ j < n, dist (T^[j] x) (T^[j] y) < ρ) →
      |orbitSum T φ n x - orbitSum T φ n y| ≤ D) :
    pressure T φ univ = limsup (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
      (separatedPartitionSum T φ univ n ρ).log) atTop := by
  apply le_antisymm
  · unfold pressure
    apply iSup_le
    intro ε
    obtain ⟨C, positive, comparison⟩ := partition_scale_comparison
      T c positiveC expansive φ ρ D positiveρ coarse bowen ε.val ε.property
    have compare : ∀ᶠ n : ℕ in atTop,
        (((n : ℝ)⁻¹ : ℝ) : EReal) * (separatedPartitionSum T φ univ n ε.val).log ≤
          (((n : ℝ)⁻¹ : ℝ) : EReal) * (separatedPartitionSum T φ univ n ρ).log +
            (((n : ℝ)⁻¹ * Real.log C : ℝ) : EReal) := by
      apply Eventually.of_forall
      intro n
      have logs := ENNReal.log_le_log (comparison n)
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos positive] at logs
      have factor : (0 : EReal) ≤ (((n : ℝ)⁻¹ : ℝ) : EReal) := EReal.coe_nonneg.mpr (by positivity)
      have scaled := mul_le_mul_of_nonneg_left logs factor
      rw [EReal.left_distrib_of_nonneg_of_ne_top factor (EReal.coe_ne_top _),
        ← EReal.coe_mul] at scaled
      simpa only [add_comm] using scaled
    have error := continuous_coe_real_ereal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_nhds_zero_nat.mul_const (Real.log C))
    simp only [Function.comp_def, zero_mul, EReal.coe_zero] at error
    have addition := EReal.limsup_add_le (f := atTop)
      (u := fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
        (separatedPartitionSum T φ univ n ρ).log)
      (v := fun n : ℕ => (((n : ℝ)⁻¹ * Real.log C : ℝ) : EReal))
      (Or.inr (by rw [error.limsup_eq]; exact EReal.zero_ne_top))
      (Or.inr (by rw [error.limsup_eq]; exact EReal.zero_ne_bot))
    rw [error.limsup_eq, add_zero] at addition
    exact (limsup_le_limsup compare).trans addition
  · exact le_iSup (fun ε : {ε : ℝ // 0 < ε} => limsup (fun n : ℕ =>
      (((n : ℝ)⁻¹ : ℝ) : EReal) * (separatedPartitionSum T φ univ n ε.val).log) atTop)
      ⟨ρ, positiveρ⟩

end LeanShared.ThermodynamicDefinitions
