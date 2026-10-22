module

public import LeanShared.Dynamics.OneSidedAbelResolvent
public import Mathlib.Analysis.Analytic.OfScalars

/-! The actual norm-coefficient Abel series has a strictly positive,
finite convergence radius.  Its interior gives genuine convergence of
the literal transfer Abel sum, beyond any fixed crude norm disk.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function Filter
open scoped Topology NNReal ENNReal
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [CompactSpace A] [Fintype A]
  {R : A → A → Prop} [Nonempty (FuturePath R)]

private theorem geometric_scalar_radius (r : ℝ≥0) (nonzero : r ≠ 0) :
    (FormalMultilinearSeries.ofScalars ℝ (fun n : ℕ => (r : ℝ) ^ n)).radius = ((r⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto ℝ _ nonzero
  have ratio (n : ℕ) : ‖(r : ℝ) ^ (n + 1)‖ / ‖(r : ℝ) ^ n‖ = (r : ℝ) := by
    change |(r : ℝ) ^ (n + 1)| / |(r : ℝ) ^ n| = (r : ℝ)
    rw [abs_of_nonneg (pow_nonneg r.coe_nonneg _), abs_of_nonneg (pow_nonneg r.coe_nonneg _), pow_succ]
    field_simp [pow_ne_zero n (NNReal.coe_ne_zero.mpr nonzero)]
  simpa only [ratio] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (r : ℝ)) atTop (𝓝 (r : ℝ)))

@[expose] def abelNormSeries (ψ : C(FuturePath R, ℝ)) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun m : ℕ => ‖weightedIterateOne ψ m‖)

@[expose] def abelRadius (ψ : C(FuturePath R, ℝ)) : ℝ≥0∞ := (abelNormSeries ψ).radius

theorem weightedTransferOperator_norm_positive (ψ : C(FuturePath R, ℝ)) :
    0 < ‖weightedTransferOperator ψ‖ := by
  have lower := weightedTransferOperator_power_norm_lower ψ 1
  simp only [pow_one] at lower
  exact (Real.exp_pos _).trans_le lower

theorem abelRadius_lower (ψ : C(FuturePath R, ℝ)) :
    (((‖weightedTransferOperator ψ‖₊)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ abelRadius ψ := by
  let r := ‖weightedTransferOperator ψ‖₊
  have nonzero : r ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast weightedTransferOperator_norm_positive ψ
  rw [← geometric_scalar_radius r nonzero]
  apply FormalMultilinearSeries.radius_le_of_le
  intro m
  simp only [abelNormSeries, FormalMultilinearSeries.ofScalars_norm, norm_norm]
  rw [← weightedTransferOperator_power_norm]
  simp only [norm_pow, NNReal.norm_eq]
  change ‖weightedTransferOperator ψ ^ m‖ ≤ ‖weightedTransferOperator ψ‖ ^ m
  exact norm_pow_le (weightedTransferOperator ψ) m

theorem abelRadius_positive (ψ : C(FuturePath R, ℝ)) : 0 < abelRadius ψ := by
  apply lt_of_lt_of_le _ (abelRadius_lower ψ)
  have positive : 0 < ‖weightedTransferOperator ψ‖₊ := by exact_mod_cast weightedTransferOperator_norm_positive ψ
  exact ENNReal.coe_pos.mpr (inv_pos.mpr positive)

theorem abelRadius_upper (ψ : C(FuturePath R, ℝ)) :
    abelRadius ψ ≤ (((Real.toNNReal (Real.exp (-‖ψ‖)))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
  let r := Real.toNNReal (Real.exp (-‖ψ‖))
  have nonzero : r ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr (Real.exp_pos _))
  rw [← geometric_scalar_radius r nonzero]
  apply FormalMultilinearSeries.radius_le_of_le
  intro m
  simp only [abelNormSeries, FormalMultilinearSeries.ofScalars_norm, norm_norm, norm_pow, NNReal.norm_eq]
  have lower := weightedTransferOperator_power_norm_lower ψ m
  rw [weightedTransferOperator_power_norm] at lower
  simpa only [r, Real.coe_toNNReal _ (Real.exp_pos _).le] using lower

theorem abelRadius_lt_top (ψ : C(FuturePath R, ℝ)) : abelRadius ψ < ∞ :=
  (abelRadius_upper ψ).trans_lt ENNReal.coe_lt_top

omit [Nonempty (FuturePath R)] in
theorem weightedAbel_summable_of_lt_radius (ψ : C(FuturePath R, ℝ)) (t : ℝ≥0)
    (inside : (t : ℝ≥0∞) < abelRadius ψ) :
    Summable (fun m : ℕ => (t : ℝ) ^ m • weightedIterateOne ψ m) := by
  have scalar := (abelNormSeries ψ).summable_norm_mul_pow inside
  apply Summable.of_norm
  convert scalar using 1
  funext m
  simp only [abelNormSeries, FormalMultilinearSeries.ofScalars_norm, norm_norm, norm_smul, norm_pow, NNReal.norm_eq]
  ring

end LeanShared.BilateralShadowingCoding
