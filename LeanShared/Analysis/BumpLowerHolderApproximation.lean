module
public import LeanShared.Analysis.BumpSupportedRegularization
public import LeanShared.Analysis.HolderInterpolation

/-! Quantitative lower-Hölder convergence of the literal smooth mollifiers.
The higher Hölder constant, uniform error and lower graph norm are all
proved for the actual convolution, rather than assumed approximation data. -/
public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace LeanShared.BumpLowerHolderApproximation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure] (φ : ContDiffBump (0 : E))
  (f : E →ᵇ ℂ) {a b C : ℝ}

@[expose] def error : E →ᵇ ℂ := BumpSupportedRegularization.bounded μ φ f - f

theorem uniform_error (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) :
    ‖error μ φ f‖ ≤ C * φ.rOut ^ a := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg hC (Real.rpow_nonneg φ.rOut_pos.le _))).mpr
  intro x
  exact BumpHolderRegularization.convolution_error μ φ f ha hC hf x

theorem higher_increment
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) (x y : E) :
    ‖error μ φ f x - error μ φ f y‖ ≤ (2 * C) * ‖x - y‖ ^ a := by
  change ‖(BumpSupportedRegularization.function μ φ f x - f x) -
    (BumpSupportedRegularization.function μ φ f y - f y)‖ ≤ _
  have eq : (BumpSupportedRegularization.function μ φ f x - f x) -
      (BumpSupportedRegularization.function μ φ f y - f y) =
      (BumpSupportedRegularization.function μ φ f x - BumpSupportedRegularization.function μ φ f y) -
        (f x - f y) := by ring
  rw [eq]
  calc
    _ ≤ ‖BumpSupportedRegularization.function μ φ f x - BumpSupportedRegularization.function μ φ f y‖ +
        ‖f x - f y‖ := norm_sub_le _ _
    _ ≤ C * ‖x - y‖ ^ a + C * ‖x - y‖ ^ a :=
      add_le_add (BumpHolderRegularization.convolution_increment μ φ f hf x y) (hf x y)
    _ = _ := by ring

theorem lower_increment (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) (x y : E) :
    ‖error μ φ f x - error μ φ f y‖ ≤ (2 * C * φ.rOut ^ (a - b)) * dist x y ^ b := by
  have hnorm := uniform_error μ φ f (hb.trans hab.le) hC hf
  have h := HolderInterpolation.increment_bound (a := a) (b := b) (C := 2 * C) (δ := φ.rOut) (error μ φ f) hb hab
    (mul_nonneg (by norm_num) hC) φ.rOut_pos
    (fun x y => by simpa only [dist_eq_norm] using higher_increment μ φ f hf x y) x y
  have divide : 2 * ‖error μ φ f‖ / φ.rOut ^ b ≤ 2 * C * φ.rOut ^ (a - b) := by
    calc
      _ ≤ 2 * (C * φ.rOut ^ a) / φ.rOut ^ b :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by norm_num))
          (Real.rpow_nonneg φ.rOut_pos.le _)
      _ = _ := by rw [Real.rpow_sub φ.rOut_pos]; ring
  exact h.trans (mul_le_mul_of_nonneg_right (max_le le_rfl divide) (Real.rpow_nonneg dist_nonneg _))

@[expose] def lowerError (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) : BoundedHolderSpace.graph E b :=
  BoundedHolderSpace.ofBound E b (error μ φ f) (2 * C * φ.rOut ^ (a - b))
    (lower_increment μ φ f hb hab hC hf)

theorem lower_error_bound (hb : 0 ≤ b) (hab : b < a) (hC : 0 ≤ C)
    (hf : ∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ a) :
    ‖lowerError μ φ f hb hab hC hf‖ ≤
      max (C * φ.rOut ^ a) (2 * C * φ.rOut ^ (a - b)) := by
  have phys : BoundedHolderSpace.physical E b (lowerError μ φ f hb hab hC hf) = error μ φ f :=
    BoundedHolderSpace.physical_ofBound _ _ _ _ _
  have bound := HolderInterpolation.graph_norm_le (C := 2 * C * φ.rOut ^ (a - b)) b (lowerError μ φ f hb hab hC hf)
    (mul_nonneg (mul_nonneg (by norm_num) hC) (Real.rpow_nonneg φ.rOut_pos.le _))
    (by rw [phys]; exact lower_increment μ φ f hb hab hC hf)
  rw [phys] at bound
  exact bound.trans (max_le_max (uniform_error μ φ f (hb.trans hab.le) hC hf) le_rfl)

end LeanShared.BumpLowerHolderApproximation
