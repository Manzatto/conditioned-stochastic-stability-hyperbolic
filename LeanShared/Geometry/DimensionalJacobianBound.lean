module

public import LeanShared.Analysis.GraphJacobian

/-! The actual Gram determinant bound is monotone in the dimension. This
makes native varying-subspace bounds uniform in the ambient dimension. -/
public noncomputable section
namespace LeanShared.DimensionalJacobianBound

@[expose] def bound (d : ℕ) (L : ℝ) : ℝ :=
  GraphJacobian.densityBound (ι := Fin d) L

theorem positive (d : ℕ) (L : ℝ) : 0 < bound d L := by
  unfold bound GraphJacobian.densityBound
  apply Real.sqrt_pos.mpr
  positivity

theorem dimension_mono {d e : ℕ} (h : d ≤ e) (L : ℝ) : bound d L ≤ bound e L := by
  unfold bound GraphJacobian.densityBound
  simp only [Fintype.card_fin]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le h
  · exact pow_le_pow_right₀ (le_add_of_nonneg_right (sq_nonneg L)) h
  · positivity
  · positivity

end LeanShared.DimensionalJacobianBound
