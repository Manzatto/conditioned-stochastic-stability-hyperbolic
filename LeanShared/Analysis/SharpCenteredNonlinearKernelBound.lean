module
public import LeanShared.Analysis.RegularisedCenteredKernelIdentity
public import LeanShared.Analysis.UniformIntegratedDirectionalKernelEnvelope
public import LeanShared.Analysis.CenteredCompactKernelIntegrable
public import LeanShared.Analysis.CenteredKernelSupport
public import LeanShared.Analysis.BanachMollifierRadiusSupport
import Mathlib.Tactic

/-! The assembled uniform fractional nonstationary kernel estimate.
The physical convolution geometry is retained. The coefficient jets
are those constructed from actual map and amplitude controls by
ActualNonlinearRegularisedResolution, rather than independent jets. -/
public noncomputable section
set_option maxHeartbeats 3000000
open Set MeasureTheory
open scoped ContDiff Convolution FourierTransform BoundedContinuousFunction RealInnerProductSpace Pointwise
namespace LeanShared.SharpCenteredNonlinearKernelBound
open HilbertFrequencyPair
variable {E:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (Space E)] [BorelSpace (Space E)]

theorem exists_bound {P ι:Type*} [Fintype ι] (μ:Measure E) [μ.IsAddHaarMeasure]
    (m:ℕ) {K:Set (Space E)} (compactK:IsCompact K)
    {κ:E→ℝ} (smoothκ:ContDiff ℝ 1 κ) (compactκ:HasCompactSupport κ)
    (ρ:ℝ) (hρ:0<ρ) (small:Function.support κ⊆Metric.closedBall 0 ρ) (mass:∫y,κ y ∂μ=1)
    (q:P→ι→E→ᵇ(SupportedFiniteJetSpace.space (2*m) K))
    {L₀:Set E} (compactL₀:IsCompact L₀)
    (supported:∀p i,tsupport (fun w=>q p i w)⊆L₀)
    {α D:ℝ} (hα:0<α) (hD:0≤D) (H:ι→ℝ) (hH:∀i,0≤H i)
    (holder:∀p i x y,‖q p i x-q p i y‖≤H i*‖x-y‖^α)
    (G:P→E→E) (smoothG:∀p,ContDiff ℝ 1 (G p)) (gv:∀p w,‖fderiv ℝ (G p) w‖≤D)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1) (v:ι→E)
    (f:P→E→Space E→ℂ) (fc:∀p,Continuous (f p).uncurry) (fs:∀p,HasCompactSupport (f p).uncurry)
    (resolution:∀p w ζ,∑i,(fderiv ℝ (NonlinearFourierPhaseGradient.phase (G p)
      (s p • (decode ζ).1) (t p • (decode ζ).2)) w (v i):ℂ)*
      SupportedJetFourierEvaluation.physical (2*m) K (q p i w) ζ=f p w ζ):
    ∃C:ℝ,0≤C ∧∀p,∀Λ:ℝ,1≤Λ→∀a b:ℝ,Λ*s p=a→Λ*t p=b→∀x y:E,
      ‖∫w,𝓕 (f p w) (-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G p w-y))) ∂μ‖≤
        C*(Λ^α)⁻¹*(∫w in L₀+Metric.closedBall 0 ρ,
          envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
            envelope m (((2*Real.pi)⁻¹*b) • (G p w-y)) ∂μ):=by
  have components (i:ι):=UniformIntegratedDirectionalKernelEnvelope.exists_bounds μ m compactK
    smoothκ compactκ mass (fun p=>q p i) hα (hH i) hD (fun p=>holder p i)
    G smoothG gv s t hs ht (v i)
  choose C₁ C₀ hC₁ hC₀ bounds using components
  let C:ℝ:=(∑i,C₁ i)+(∑i,C₀ i)
  have hC:0≤C:=add_nonneg (Finset.sum_nonneg (fun i _=>hC₁ i))
    (Finset.sum_nonneg (fun i _=>hC₀ i))
  refine ⟨C,hC,?_⟩
  intro p Λ large a b ha hb x y
  have hΛ:0<Λ:=zero_lt_one.trans_le large
  let L:Set E:=L₀+Metric.closedBall 0 ρ
  have compactL:IsCompact L:=compactL₀.add (isCompact_closedBall 0 ρ)
  have subL:L₀⊆L:=by
    intro w hw
    exact ⟨w,hw,0,by simpa using hρ.le,by simp⟩
  let qr:ι→E→SupportedFiniteJetSpace.space (2*m) K:=fun i=>
    BanachNormalizedKernelDilation.dilate κ Λ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun w=>q p i w)
  have regular (i:ι):ContDiff ℝ 1 (qr i):=
    (BanachNormalizedKernelDilation.compact compactκ hΛ).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (BanachNormalizedKernelDilation.smooth smoothκ Λ)
      ((q p i).continuous.locallyIntegrable (μ:=μ))
  have supportqr (i:ι):tsupport (qr i)⊆L:=
    BanachMollifierRadiusSupport.support_subset μ ρ small (q p i) compactL₀ (supported p i) large
  have compactq (i:ι):HasCompactSupport (fun w=>q p i w):=
    compactL₀.of_isClosed_subset (isClosed_tsupport _) (supported p i)
  have compactqr (i:ι):HasCompactSupport (qr i):=
    compactL.of_isClosed_subset (isClosed_tsupport _) (supportqr i)
  let d:ι→E→Space E→ℂ:=fun i w ζ=>fderiv ℝ
    (fun w'=>SupportedJetFourierEvaluation.physical (2*m) K (qr i w') ζ) w (v i)
  let r:ι→E→Space E→ℂ:=fun i w ζ=>
    (fderiv ℝ (NonlinearFourierPhaseGradient.phase (G p) (s p • (decode ζ).1) (t p • (decode ζ).2)) w (v i):ℂ)*
      SupportedJetFourierEvaluation.physical (2*m) K (q p i w-qr i w) ζ
  have dc (i:ι):Continuous (d i).uncurry:=CompatiblePhysicalDerivative.continuous_joint (2*m) K (regular i) (v i)
  have ds (i:ι):HasCompactSupport (d i).uncurry:=
    CompatiblePhysicalDerivative.compact_joint (2*m) compactK (regular i) (compactqr i) (v i)
  have rc (i:ι):Continuous (r i).uncurry:=
    NonlinearJetResidualFamily.continuous_residual (G p) (smoothG p) (s p) (t p) (v i) (2*m) K
      ((q p i).continuous.sub (regular i).continuous)
  have rs (i:ι):HasCompactSupport (r i).uncurry:=
    NonlinearJetResidualFamily.compact_residual (G p) (s p) (t p) (v i) (2*m) compactK
      (q:=fun w=>q p i w-qr i w) ((compactq i).sub (compactqr i))
  let z:E→Space E:=fun w=>-(2*Real.pi)⁻¹ • encode (a • (x-w)) (b • (G p w-y))
  let A:ℂ:=∫w,𝓕 (f p w) (z w) ∂μ
  let B:ι→ℂ:=fun i=>∫w,𝓕 (d i w) (z w) ∂μ
  let R:ι→ℂ:=fun i=>∫w,𝓕 (r i w) (z w) ∂μ
  let J:ℝ:=∫w in L,envelope m (((2*Real.pi)⁻¹*a) • (x-w))*
    envelope m (((2*Real.pi)⁻¹*b) • (G p w-y)) ∂μ
  have hJ:0≤J:=integral_nonneg (fun _=>by dsimp [envelope];positivity)
  have Bbound (i:ι):‖B i‖≤C₁ i*(Λ*(Λ^α)⁻¹)*J:=by
    have eqn:B i=∫w in L,𝓕 (d i w) (z w) ∂μ:=by
      dsimp only [B,d]
      simp_rw [CompatiblePhysicalDerivative.formula (2*m) K (regular i)]
      simpa only [one_mul] using CenteredKernelSupport.multiplier_restrict μ (2*m) K
        (fun w=>fderiv ℝ (qr i) w (v i))
        (CenteredKernelSupport.derivative_support (2*m) K (qr i) (supportqr i) (v i))
        (fun _ _=>1) z
    rw [eqn]
    exact (bounds i p Λ hΛ L compactL x y a b).1
  have Rbound (i:ι):‖R i‖≤C₀ i*(Λ^α)⁻¹*J:=by
    have supportdiff:tsupport (fun w=>q p i w-qr i w)⊆L:=
      (tsupport_binop_subset (·-·) (by simp) (fun w=>q p i w) (qr i)).trans
        (union_subset ((supported p i).trans subL) (supportqr i))
    have eqn:R i=∫w in L,𝓕 (r i w) (z w) ∂μ:=
      CenteredKernelSupport.multiplier_restrict μ (2*m) K (fun w=>q p i w-qr i w) supportdiff
        (fun w ζ=>(fderiv ℝ (NonlinearFourierPhaseGradient.phase (G p)
          (s p • (decode ζ).1) (t p • (decode ζ).2)) w (v i):ℂ)) z
    rw [eqn]
    exact (bounds i p Λ hΛ L compactL x y a b).2
  have identity:=RegularisedCenteredKernelIdentity.identity μ (2*m) compactK
    (BanachNormalizedKernelDilation.smooth smoothκ Λ)
    (BanachNormalizedKernelDilation.compact compactκ hΛ) (q p) compactq (G p) (smoothG p) v
    a b Λ (s p) (t p) ha hb hΛ.ne' (f p) (fc p) (fs p) (resolution p) x y
  change -Complex.I*A=(Λ:ℂ)⁻¹*
    (∫w,𝓕 (fun ζ=>∑i,d i w ζ) (z w) ∂μ)+
    -Complex.I*(∫w,𝓕 (fun ζ=>∑i,r i w ζ) (z w) ∂μ) at identity
  rw [CenteredCompactKernelIntegrable.integral_fourier_sum μ (G p) (smoothG p).continuous
    a b x y d dc ds,CenteredCompactKernelIntegrable.integral_fourier_sum μ (G p) (smoothG p).continuous
    a b x y r rc rs] at identity
  have raw:‖A‖≤Λ⁻¹*(∑i,‖B i‖)+(∑i,‖R i‖):=by
    calc
      _ = ‖-Complex.I*A‖:=by simp
      _ = _:=congrArg norm identity
      _ ≤ _:=norm_add_le _ _
      _ = |Λ|⁻¹*‖∑i,B i‖+‖∑i,R i‖:=by simp only [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,norm_neg,Complex.norm_I,one_mul];rfl
      _ ≤ _:=by rw [abs_of_pos hΛ];exact add_le_add (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hΛ.le)) (norm_sum_le _ _)
  have estimate:‖A‖≤Λ⁻¹*(∑i,C₁ i*(Λ*(Λ^α)⁻¹)*J)+(∑i,C₀ i*(Λ^α)⁻¹*J):=
    raw.trans (add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>Bbound i))
      (inv_nonneg.mpr hΛ.le)) (Finset.sum_le_sum (fun i _=>Rbound i)))
  exact estimate.trans_eq (by
    change Λ⁻¹*(∑i,C₁ i*(Λ*(Λ^α)⁻¹)*J)+(∑i,C₀ i*(Λ^α)⁻¹*J)=C*(Λ^α)⁻¹*J
    simp only [←Finset.sum_mul]
    dsimp only [C]
    field_simp [hΛ.ne', (Real.rpow_pos_of_pos hΛ α).ne'])
end LeanShared.SharpCenteredNonlinearKernelBound
