module
public import LeanShared.Analysis.FourierHigherTaylorCancellation
public import LeanShared.Analysis.HigherTaylorSupportBound
public import LeanShared.Analysis.SchwartzWeightedRealMoment

/-! Full finite-order fractional cancellation bound for the literal Fourier
convolution, including spatial decay. No moment or operator estimate is assumed. -/
public noncomputable section
open MeasureTheory Filter Set
open scoped SchwartzMap BoundedContinuousFunction Topology
namespace LeanShared.WeightedHigherFourierConvolution
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] (b:OrthonormalBasis ι ℝ E)

include b in
theorem bound (σ:𝓢(E,ℂ)) (zero:∀ᶠ ξ in 𝓝 (0:E),σ ξ=0)
    (f:E→ᵇℂ) (n:ℕ) (smooth:ContDiff ℝ (n+1) f) {a C R:ℝ}
    (ha:0≤a) (hC:0≤C) (hR:0≤R)
    (support:∀z∈tsupport f,‖z‖≤R)
    (holder:∀z w,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f w‖≤C*‖z-w‖^a)
    (m:ℕ) (x:E) :
    (1+‖x‖)^m*‖∫y,FourierSchwartzKernel.kernel σ y*f (x-y)‖≤
      |(n.factorial:ℝ)⁻¹| * C*
        ∫y,‖FourierSchwartzKernel.kernel σ y‖*‖y‖^(a+(n+1:ℕ))*(1+R+‖y‖)^m := by
  let k:=FourierSchwartzKernel.kernel σ
  let p:=fun y=>HigherHolderTaylorRemainder.polynomial f n x (-y)
  have product:Integrable (fun y=>k y*f (x-y)) :=
    k.integrable.mul_bdd (f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y=>f.norm_coe_le_norm (x-y))
  have poly:Integrable (fun y=>k y*p y) :=
    FourierHigherTaylorCancellation.integrable_polynomial b σ f n x (-ContinuousLinearMap.id ℝ E)
  have vanish:(∫y,k y*p y)=0 :=
    FourierHigherTaylorCancellation.polynomial_zero b σ zero f n x (-ContinuousLinearMap.id ℝ E)
  have subtract:(∫y,k y*(f (x-y)-p y))=∫y,k y*f (x-y) := by
    simp_rw [mul_sub]
    rw [integral_sub product poly,vanish,sub_zero]
  have moment:=SchwartzHolderMoments.polynomial_integrable_any volume k
    (by positivity : 0≤a+(n+1:ℕ)) hR m
  rw [←subtract]
  calc
    _ ≤ (1+‖x‖)^m*∫y,‖k y*(f (x-y)-p y)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫y,(1+‖x‖)^m*‖k y*(f (x-y)-p y)‖ := (integral_const_mul _ _).symm
    _ ≤ ∫y,(|(n.factorial:ℝ)⁻¹| * C)*(‖k y‖*‖y‖^(a+(n+1:ℕ))*(1+R+‖y‖)^m) :=
      integral_mono_of_nonneg (ae_of_all _ fun y=>by positivity)
        (moment.const_mul (|(n.factorial:ℝ)⁻¹| * C)) (ae_of_all _ fun y=>by
          have estimate:=HigherTaylorSupportBound.difference_bound f n smooth ha hC hR support holder m x y
          have multiplied:=mul_le_mul_of_nonneg_left estimate (norm_nonneg (k y))
          change (1+‖x‖)^m*‖k y*(f (x-y)-p y)‖≤_
          rw [norm_mul]
          dsimp only [p]
          nlinarith only [multiplied])
    _ = _ := integral_const_mul _ _
end LeanShared.WeightedHigherFourierConvolution
