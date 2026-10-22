module
public import LeanShared.Analysis.WeightedHigherFourierConvolution
public import LeanShared.Analysis.FourierWeightedRealMomentDilation
public import LeanShared.Analysis.ConeDyadicKernelMoments
public import LeanShared.Analysis.GraphLeafNorm

/-! Arbitrary-order fractional decay for the literal dyadic blocks,
with a uniform spatial envelope derived from actual higher derivatives. -/
public noncomputable section
open Set Filter MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction Topology
namespace LeanShared.FourierHigherRadialEnvelope
open FourierSchwartzKernel
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] (b:OrthonormalBasis ι ℝ E)

include b in
theorem exists_envelope (σ:𝓢(E,ℂ)) (zero:∀ᶠξ in 𝓝 (0:E),σ ξ=0)
    {K:Set E} (compact:IsCompact K) {a:ℝ} (ha:0≤a) (n m:ℕ) :
    ∃B:ℝ,0≤B ∧ ∀(f:E→ᵇℂ) (C:ℝ),0≤C→ContDiff ℝ (n+1) f→tsupport f⊆K→
      (∀z w,‖iteratedFDeriv ℝ (n+1) f z-iteratedFDeriv ℝ (n+1) f w‖≤C*‖z-w‖^a)→
      ∀r:ℝ,∀hr:1≤r,∀x:E,
      ‖∫y,kernel (dilateSymbol σ r (by linarith)) y*f (x-y)‖≤
        B*C*(r^(a+(n+1:ℕ)))⁻¹*GraphLeafNorm.radialWeight (m:ℝ) x := by
  obtain ⟨R,hR,radius⟩:=compact.isBounded.exists_pos_norm_le
  let I:ℝ:=∫y,‖kernel σ y‖*‖y‖^(a+(n+1:ℕ))*(1+R+‖y‖)^m
  let B:ℝ:=|(n.factorial:ℝ)⁻¹| * I
  have hI:0≤I:=integral_nonneg (fun y=>by positivity)
  refine ⟨B,mul_nonneg (abs_nonneg _) hI,?_⟩
  intro f C hC smooth support holder r hr x
  have bound:=WeightedHigherFourierConvolution.bound b (dilateSymbol σ r (by linarith))
    (ConeDyadicKernelMoments.dilate_eventually_zero σ zero r (by linarith))
    f n smooth ha hC hR.le (fun z hz=>radius z (support hz)) holder m x
  have moment:=weighted_norm_kernel_dilate_le_any σ hr
    (by positivity : 0≤a+(n+1:ℕ)) hR.le m
  calc
    _ ≤ (|(n.factorial:ℝ)⁻¹| * C*((r^(a+(n+1:ℕ)))⁻¹*I))/(1+‖x‖)^m := by
      exact (le_div_iff₀ (by positivity)).mpr (by simpa only [I,mul_comm] using
        (bound.trans (mul_le_mul_of_nonneg_left moment (mul_nonneg (abs_nonneg _) hC))))
    _ = _ := by
      rw [GraphLeafNorm.radialWeight,Real.rpow_neg (by positivity),Real.rpow_natCast]
      dsimp only [B]
      ring
end LeanShared.FourierHigherRadialEnvelope
