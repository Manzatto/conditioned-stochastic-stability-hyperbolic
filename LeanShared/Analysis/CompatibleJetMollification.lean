module
public import LeanShared.Analysis.BoundedFiniteJetEvaluation
public import LeanShared.Analysis.BanachScaledHolderMollification

/-! Actual convolution regularizes the entire compatible frequency jet.
Every retained frequency derivative is the convolution of its genuine
original derivative, by a bounded evaluation map and Bochner linearity. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff Convolution BoundedContinuousFunction
namespace LeanShared.CompatibleJetMollification
variable {Z:Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

abbrev Jet (Z:Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (n:ℕ):=
  (BoundedFiniteJetSpace.construct (E:=Z) n (F:=ℂ)).carrier

theorem frequency_derivative_formula (μ:Measure E) [μ.IsAddHaarMeasure]
    (n j:ℕ) (hj:j≤n) {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (q:E→ᵇJet Z n) (x:E) (z:Z):
    iteratedFDeriv ℝ j ((BoundedFiniteJetSpace.construct n (F:=ℂ)).physical
      ((κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)) x)) z=
      ∫y,κ y • iteratedFDeriv ℝ j
        ((BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (q (x-y))) z ∂μ:=by
  let ev:=BoundedFiniteJetSpace.evaluation (E:=Z) (F:=ℂ) n j hj z
  let L:ℝ→L[ℝ]Jet Z n→L[ℝ]Jet Z n:=ContinuousLinearMap.lsmul ℝ ℝ
  have integrable:Integrable (fun y=>κ y • q (x-y)) μ:=
    compact.convolutionExists_left L smooth.continuous (q.continuous.locallyIntegrable (μ:=μ)) x
  change ev ((κ ⋆[L,μ] (fun y=>q y)) x)=∫y,κ y • ev (q (x-y)) ∂μ
  rw [convolution_def]
  change ev (∫y,κ y • q (x-y) ∂μ)=∫y,κ y • ev (q (x-y)) ∂μ
  rw [←ev.integral_comp_comm integrable]
  apply integral_congr_ae
  filter_upwards with y
  exact ev.map_smul_of_tower (κ y) (q (x-y))

theorem scaled_controls (μ:Measure E) [μ.IsAddHaarMeasure] (n:ℕ)
    {κ:E→ℝ} (smooth:ContDiff ℝ 1 κ) (compact:HasCompactSupport κ)
    (mass:∫y,κ y ∂μ=1) (q:E→ᵇJet Z n) {a H r:ℝ}
    (ha:0<a) (hH:0≤H) (holder:∀x y,‖q x-q y‖≤H*‖x-y‖^a) (hr:0<r):
    let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
    ContDiff ℝ 1 qr ∧
      (∀x,‖qr x-q x‖≤H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ)) ∧
      (∀x,‖fderiv ℝ qr x‖≤H*(r*(r^a)⁻¹)*(∫y,‖fderiv ℝ κ y‖*‖y‖^a ∂μ)) ∧
      ∀j≤n,∀x z,
        ‖iteratedFDeriv ℝ j ((BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (qr x)) z-
          iteratedFDeriv ℝ j ((BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (q x)) z‖≤
          H*(r^a)⁻¹*(∫y,‖κ y‖*‖y‖^a ∂μ):=by
  let qr:=BanachNormalizedKernelDilation.dilate κ r ⋆[ContinuousLinearMap.lsmul ℝ ℝ,μ] (fun y=>q y)
  have error:=BanachScaledHolderMollification.scaled_error μ smooth.continuous compact mass q ha hH holder hr
  have derivative:=BanachScaledHolderMollification.scaled_derivative μ smooth compact q ha hH holder hr
  refine ⟨(BanachNormalizedKernelDilation.compact compact hr).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (BanachNormalizedKernelDilation.smooth smooth r)
    (q.continuous.locallyIntegrable (μ:=μ)),error,derivative,?_⟩
  intro j hj x z
  let ev:=BoundedFiniteJetSpace.evaluation (E:=Z) (F:=ℂ) n j hj z
  change ‖ev (qr x)-ev (q x)‖≤_
  rw [←map_sub]
  exact (BoundedFiniteJetSpace.derivative_le n (qr x-q x) j hj z).trans (error x)
end LeanShared.CompatibleJetMollification
