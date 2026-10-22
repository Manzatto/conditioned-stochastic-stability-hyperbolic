module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderNoiseImageModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderNoiseInterpolation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldNoiseSources

/-! All original noise-source fields for the actual lower Holder physical
model, constructed from the literal regular noise family. The power estimate
is proved through a common higher-order window. -/
public noncomputable section
set_option maxHeartbeats 1800000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderProvedNoiseSources
open LeanShared ConstructedHolderPhysicalModel ConstructedHolderSingleTransfer Paper
variable {E U M J A ι:Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μE:Measure E) [μE.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)
  {T:M≃ₜM} {r:ℝ} (F:Paper.RegularNoise.Maps (E:=E) (ι:=ι) T r) (hr:1≤r)
  (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g:M→ℝ} {q:ℝ} (hbq:b<q)
  (hg:FractionalManifoldRegularity.Regular (E:=E) (F:=ℝ) q g)
  (support:tsupport g⊆V)
  (η:NNReal) (cap:η≤(ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).window)


variable (μ:Measure U) [μ.IsAddHaarMeasure] {slope:ℝ} (hSlope:0≤slope)
  (leaves:D.indices→A→GraphLeafNorm.GraphLeaf U E slope)
  (plus minus:D.indices→Set E) (radial:D.indices→ConeDyadicSymbols.RadialCutoff)
  (angle:∀i,ConeDyadicSymbols.AngularCutoff (plus i) (minus i))
  (exponent:D.indices→Bool→ℝ) (margin:∀i a,exponent i a≤b)
  (lossH lossW:D.indices→ℝ) (hH:∀i,0<lossH i) (hW:∀i,0<lossW i)
  (extraH extraW:D.indices→Bool→ℝ) (hEH:∀i a,0≤extraH i a) (hEW:∀i a,0≤extraW i a)

variable {a:ℝ} (ha:0<a) (ha1:a<1) (hab:b<a) (haq:a<q)
  (capHigh:η≤(ConstructedHolderNoiseAction.bounds μE e D atlas openV region ha ha1 F hr hT haq hg support).window)

include ha hab capHigh in
@[expose] def data : PhysicalManifoldNoiseSources.Data (ConstructedHolderNoiseImageModel.model μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap
      μ hSlope leaves plus minus radial angle exponent margin lossH lossW hH hW extraH extraW hEH hEW) := by
  classical
  let m:=ConstructedHolderNoiseImageModel.model μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap
      μ hSlope leaves plus minus radial angle exponent margin lossH lossW hH hW extraH extraW hEH hEW
  let noisy:=ConstructedHolderTransferInterpolation.action μE e D atlas openV region hb hb1 hbq hg support
      (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
  have same : ∀p c,FiniteRegularTransferRealization.regularAction
      (SmoothSupportedManifoldCore.functions V) (Regular e D openV hb hb1)
      m.view m.view_injective m.maps m.weight m.coreRegular p c=noisy p c := by
    intro p c
    apply m.view_injective
    ext x
    rw [FiniteRegularTransferRealization.regularAction_apply]
    change (g x:ℂ)*c.val (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap p x)=
      view e D openV hb hb1 (noisy p c) x
    change (g x:ℂ)*c.val (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap p x)=
      view e D openV hb hb1
        (transfer μE e D atlas openV region hb hb1
          (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap p) (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap p) hbq hg support
          (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)) x
    rw [transfer_function]
    change (g x:ℂ)*c.val (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap p x)=
      (g x:ℂ)*ManifoldSmoothHolderCore.physical e D openV hb hb1
        (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c) (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap p x)
    rw [ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region]
  have estimate (c:SmoothSupportedManifoldCore.core (E:=E) V):=
    ConstructedHolderNoiseInterpolation.exists_power_bound μE e D atlas openV region hb hb1 F hr hT hbq hg support ha ha1 hab haq η cap capHigh c
  refine {
    T:=RegularNoise.MapImage.reference F hr η _
    joint:=RegularNoise.MapImage.evaluation_continuous F hr η _
    weight_continuous:=hg.differentiable.continuous
    exponent:=(a-b)/a
    exponent_positive:=div_pos (sub_pos.mpr hab) ha
    constant:=fun c _=>Classical.choose (estimate c)
    interpolation:=?_ }
  intro c p t ε hε error
  rw [same,same]
  apply (Classical.choose_spec (estimate c)).2 t p ε hε
  intro x
  have h:=error x
  change ‖m.view (FiniteRegularTransferRealization.regularAction
    (SmoothSupportedManifoldCore.functions V) (Regular e D openV hb hb1)
    m.view m.view_injective m.maps m.weight m.coreRegular t c) x-
    m.view (FiniteRegularTransferRealization.regularAction
    (SmoothSupportedManifoldCore.functions V) (Regular e D openV hb hb1)
    m.view m.view_injective m.maps m.weight m.coreRegular p c) x‖≤ε at h
  rw [same,same] at h
  exact h
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderProvedNoiseSources
