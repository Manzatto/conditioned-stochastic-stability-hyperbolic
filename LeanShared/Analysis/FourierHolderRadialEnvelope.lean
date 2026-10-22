module
public import LeanShared.Analysis.WeightedHolderConvolution
public import LeanShared.Analysis.FourierWeightedMomentDilation
public import LeanShared.Analysis.FourierKernelIntegral
public import LeanShared.Analysis.GraphLeafNorm
public import LeanShared.Geometry.BoundedHolderSpace

/-! Uniform spatial and frequency decay from the actual smooth symbol,
zero mean, compact support and a genuine Hölder graph norm. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction
namespace LeanShared.FourierHolderRadialEnvelope
open FourierSchwartzKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

include E in
theorem exists_envelope (σ : 𝓢(E,ℂ)) (zero : σ 0=0)
    {K : Set E} (compact : IsCompact K) {a : ℝ} (ha : 0<a) (ha1 : a≤1) (m : ℕ) :
    ∃ A : ℝ, 0≤A ∧ ∀ (v : BoundedHolderSpace.graph E a),
      tsupport (BoundedHolderSpace.physical E a v) ⊆ K →
      ∀ r : ℝ, ∀ hr : 1≤r, ∀ x : E,
      ‖∫ y, kernel (dilateSymbol σ r (by linarith)) y *
        BoundedHolderSpace.physical E a v (x-y)‖ ≤
        A * ‖v‖ * (r^a)⁻¹ * GraphLeafNorm.radialWeight (m : ℝ) x := by
  obtain ⟨R,hR,radius⟩ := compact.isBounded.exists_pos_norm_le
  let A : ℝ := ∫ y, ‖kernel σ y‖ * ‖y‖^a * (1+R+‖y‖)^m
  refine ⟨A, integral_nonneg (fun y => by positivity), ?_⟩
  intro v support r hr x
  have positive : 0<r := lt_of_lt_of_le zero_lt_one hr
  let f := BoundedHolderSpace.physical E a v
  have radiusF (z : E) (nonzero : f z ≠ 0) : ‖z‖≤R :=
    radius z (support (subset_tsupport _ nonzero))
  have holder (z w : E) : ‖f z-f w‖ ≤ ‖v‖*‖z-w‖^a := by
    simpa only [dist_eq_norm] using BoundedHolderSpace.increment_bound E a v z w
  have symbolZero : dilateSymbol σ r positive 0=0 := by
    simpa only [dilateSymbol_apply, smul_zero] using zero
  have bound := WeightedHolderConvolution.bound
    (kernel (dilateSymbol σ r positive)) (kernel_integrable _)
    (integral_kernel_zero _ symbolZero) f (norm_nonneg v) hR.le radiusF holder m
    (SchwartzHolderMoments.polynomial_integrable volume _ ha ha1 hR.le m) x
  have moment := weighted_norm_kernel_dilate_le σ hr ha ha1 hR.le m
  have weighted := bound.trans (mul_le_mul_of_nonneg_left moment (norm_nonneg v))
  have divide : ‖∫ y,kernel (dilateSymbol σ r positive) y*f (x-y)‖ ≤
      (‖v‖*(r^a)⁻¹*A) / (1+‖x‖)^m := by
    apply (le_div_iff₀ (by positivity : 0<(1+‖x‖)^m)).mpr
    nlinarith only [weighted]
  calc
    _ ≤ (‖v‖*(r^a)⁻¹*A) / (1+‖x‖)^m := divide
    _ = _ := by
      rw [GraphLeafNorm.radialWeight, Real.rpow_neg (by positivity), Real.rpow_natCast]
      ring
end LeanShared.FourierHolderRadialEnvelope
