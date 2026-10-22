module

public import LeanShared.Dynamics.OneSidedAbelBlowup
public import Mathlib.Analysis.SpecificLimits.Basic

/-! An explicit sequence of genuine interior Abel parameters approaches
the actual finite radius.  Its resolvent norms grow at least as n+2,
so their inverses actually tend to zero.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

@[expose] def abelApproachParameter (ψ : C(FuturePath R, ℝ)) (n : ℕ) : ℝ≥0 :=
  ⟨abelRadiusReal ψ * ((n : ℝ) + 1) / ((n : ℝ) + 2), by
    have positive := abelRadiusReal_positive ψ
    positivity⟩

theorem abelApproachParameter_positive (ψ : C(FuturePath R, ℝ)) (n : ℕ) :
    0 < abelApproachParameter ψ n := by
  change 0 < abelRadiusReal ψ * ((n : ℝ) + 1) / ((n : ℝ) + 2)
  have positive := abelRadiusReal_positive ψ
  positivity

theorem abelApproachParameter_inside (ψ : C(FuturePath R, ℝ)) (n : ℕ) :
    (abelApproachParameter ψ n : ℝ≥0∞) < abelRadius ψ := by
  apply (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (abelRadius_lt_top ψ).ne).mp
  change abelRadiusReal ψ * ((n : ℝ) + 1) / ((n : ℝ) + 2) < abelRadiusReal ψ
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)).mpr
  nlinarith [abelRadiusReal_positive ψ]

theorem abelApproachParameter_gap (ψ : C(FuturePath R, ℝ)) (n : ℕ) :
    abelRadiusReal ψ - abelApproachParameter ψ n = abelRadiusReal ψ / ((n : ℝ) + 2) := by
  change abelRadiusReal ψ - abelRadiusReal ψ * ((n : ℝ) + 1) / ((n : ℝ) + 2) = _
  field_simp
  ring

theorem abelApproachParameter_tendsto (ψ : C(FuturePath R, ℝ)) :
    Tendsto (fun n : ℕ => (abelApproachParameter ψ n : ℝ)) atTop (𝓝 (abelRadiusReal ψ)) := by
  have reciprocal : Tendsto (fun n : ℕ => abelRadiusReal ψ / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).2 (tendsto_const_div_atTop_nhds_zero_nat (abelRadiusReal ψ))
  have identity : (fun n : ℕ => (abelApproachParameter ψ n : ℝ)) =
      (fun n : ℕ => abelRadiusReal ψ - abelRadiusReal ψ / ((n : ℝ) + 2)) := by
    funext n
    linarith [abelApproachParameter_gap ψ n]
  rw [identity]
  simpa only [sub_zero] using tendsto_const_nhds.sub reciprocal

theorem weightedAbel_approach_norm_lower (ψ : C(FuturePath R, ℝ)) (n : ℕ) :
    (n : ℝ) + 2 ≤ ‖weightedAbel ψ (abelApproachParameter ψ n)‖ := by
  have lower := weightedAbel_norm_radius_lower ψ (abelApproachParameter ψ n)
    (abelApproachParameter_positive ψ n) (abelApproachParameter_inside ψ n)
  rw [abelApproachParameter_gap] at lower
  have cancel : abelRadiusReal ψ / (abelRadiusReal ψ / ((n : ℝ) + 2)) = (n : ℝ) + 2 := by
    field_simp [(abelRadiusReal_positive ψ).ne']
  rw [cancel] at lower
  exact lower

theorem weightedAbel_approach_norm_inv_tendsto_zero (ψ : C(FuturePath R, ℝ)) :
    Tendsto (fun n : ℕ => ‖weightedAbel ψ (abelApproachParameter ψ n)‖⁻¹) atTop (𝓝 0) := by
  have reciprocal : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_add_atTop_iff_nat 2).2 (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero (fun _ => inv_nonneg.mpr (norm_nonneg _)) _ reciprocal
  intro n
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 2)
    (weightedAbel_approach_norm_lower ψ n)

end LeanShared.BilateralShadowingCoding
