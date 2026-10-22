module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! A positive operator on real continuous functions has norm equal to
the norm of its actual image of one.  The same holds for every literal
operator power, so positivity supplies sharp growth data.
-/

public noncomputable section
namespace LeanShared.PositiveContinuousOperatorNorm
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

@[expose] def Positive (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) : Prop :=
  ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ L f x

omit [CompactSpace X] [Nonempty X] in
theorem monotone_apply (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (positive : Positive L)
    (f g : C(X, ℝ)) (ordered : ∀ x, f x ≤ g x) (x : X) : L f x ≤ L g x := by
  have image := positive (g - f) (fun y => sub_nonneg.mpr (ordered y)) x
  simpa only [map_sub, ContinuousMap.sub_apply, sub_nonneg] using image

omit [Nonempty X] in
theorem image_abs_bound (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (positive : Positive L)
    (f : C(X, ℝ)) (x : X) : |L f x| ≤ ‖f‖ * L 1 x := by
  have upper := monotone_apply L positive f (‖f‖ • (1 : C(X, ℝ)))
    (fun y => by change f y ≤ ‖f‖ * 1; simpa only [mul_one] using ContinuousMap.apply_le_norm f y) x
  have lower := monotone_apply L positive (-f) (‖f‖ • (1 : C(X, ℝ)))
    (fun y => by change -f y ≤ ‖f‖ * 1; have h := ContinuousMap.neg_norm_le_apply f y; linarith) x
  simp only [map_smul, map_neg, ContinuousMap.smul_apply, ContinuousMap.neg_apply,
    smul_eq_mul] at upper lower
  exact abs_le.mpr ⟨by linarith, upper⟩

theorem norm_eq_image_one (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (positive : Positive L) :
    ‖L‖ = ‖L 1‖ := by
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    intro x
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖f‖ * L 1 x := image_abs_bound L positive f x
      _ ≤ ‖f‖ * ‖L 1‖ := mul_le_mul_of_nonneg_left (ContinuousMap.apply_le_norm (L 1) x) (norm_nonneg f)
      _ = _ := mul_comm _ _
  · simpa only [norm_one, mul_one] using L.le_opNorm (1 : C(X, ℝ))

omit [Nonempty X] in
theorem power_positive (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (positive : Positive L) (n : ℕ) :
    Positive (L ^ n) := by
  induction n with
  | zero => intro f nonnegative x; exact nonnegative x
  | succ n induction =>
    intro f nonnegative x
    rw [pow_succ']
    exact positive ((L ^ n) f) (induction f nonnegative) x

theorem power_norm_eq_image_one (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (positive : Positive L) (n : ℕ) :
    ‖L ^ n‖ = ‖(L ^ n) 1‖ := norm_eq_image_one _ (power_positive L positive n)

end LeanShared.PositiveContinuousOperatorNorm
