module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderNoiseImage
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderTransferContinuity

/-! Literal small-noise core interpolation and continuity. A common cap below
two constructed windows supplies the higher bound internally. No interpolation,
regular-action norm bound, or continuity across noise scales is assumed. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseInterpolation
open LeanShared ConstructedHolderPhysicalModel ConstructedHolderSingleTransfer Paper
variable {E M J ι:Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μE:Measure E) [μE.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀ j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)
  {T:M≃ₜM} {r:ℝ} (F:RegularNoise.Maps (E:=E) (ι:=ι) T r) (hr:1≤r)
  (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
  {g:M→ℝ} {q:ℝ} (hbq:b<q)
  (hg:FractionalManifoldRegularity.Regular (E:=E) (F:=ℝ) q g)
  (support:tsupport g⊆V)

variable {a:ℝ} (ha:0<a) (ha1:a<1) (hab:b<a) (haq:a<q)
  (η:NNReal)
  (cap:η≤(ConstructedHolderNoiseAction.bounds μE e D atlas openV region hb hb1 F hr hT hbq hg support).window)
  (capHigh:η≤(ConstructedHolderNoiseAction.bounds μE e D atlas openV region ha ha1 F hr hT haq hg support).window)

include capHigh hab in
theorem exists_power_bound (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    ∃K:ℝ,0≤K ∧ ∀p t ε,0≤ε→
      (∀x,‖view e D openV hb hb1
        (ConstructedHolderTransferInterpolation.action μE e D atlas openV region hb hb1 hbq hg support
          (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
          (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) p c) x-
        view e D openV hb hb1
        (ConstructedHolderTransferInterpolation.action μE e D atlas openV region hb hb1 hbq hg support
          (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
          (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) t c) x‖≤ε)→
      dist (ConstructedHolderTransferInterpolation.action μE e D atlas openV region hb hb1 hbq hg support
          (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
          (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) p c)
        (ConstructedHolderTransferInterpolation.action μE e D atlas openV region hb hb1 hbq hg support
          (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
          (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) t c) ≤K*ε^((a-b)/a) := by
  apply ConstructedHolderTransferInterpolation.exists_power_bound μE e D atlas openV region hb hb1 hbq hg support
    ha ha1 hab haq (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
    (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
    (B:=ConstructedHolderNoiseAction.constant μE e D atlas openV region ha ha1 F hr hT haq hg support) ?_ ?_ c
  · exact le_trans (norm_nonneg _) (le_max_left _ _)
  · intro p
    exact ConstructedHolderNoiseImage.operator_bound μE e D atlas openV region ha ha1 F hr hT haq hg support η capHigh p

include capHigh hab in
theorem core_continuous (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    Continuous (fun p=>ConstructedHolderTransferInterpolation.action μE e D atlas openV region hb hb1 hbq hg support
      (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
      (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) p c) := by
  apply ConstructedHolderTransferContinuity.continuous_action μE e D atlas openV region hb hb1 hbq hg support
    ha ha1 hab haq (ConstructedHolderNoiseImage.maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
    (ConstructedHolderNoiseImage.regular μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
    (B:=ConstructedHolderNoiseAction.constant μE e D atlas openV region ha ha1 F hr hT haq hg support) ?_ ?_ ?_ c
  · exact le_trans (norm_nonneg _) (le_max_left _ _)
  · intro p
    exact ConstructedHolderNoiseImage.operator_bound μE e D atlas openV region ha ha1 F hr hT haq hg support η capHigh p
  · exact RegularNoise.MapImage.evaluation_continuous F hr η _
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseInterpolation
