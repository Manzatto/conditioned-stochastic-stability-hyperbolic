module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderNoiseImage
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderCompactModel
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderPhysicalNorm

/-! Literal regular noise maps and a supported finite-C^q weight construct every
regular-action field of the physical model. The exponent between β and
min(1,r) is chosen internally. No action membership or norm bound is input. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseImageModel
open ConstructedHolderNoiseImage
open LeanShared ConstructedHolderPhysicalModel
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

/-- Every physical model field is constructed from genuine F/g and the
actual chart geometry. The actual small positive-scale noise family and its deterministic reference
are retained; no regular action bound is supplied. -/
@[expose] def model := ConstructedHolderPhysicalModel.model (Ω:=Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
  e D atlas openV region hb hb1 μ hSlope leaves plus minus radial angle exponent margin
  lossH lossW hH hW extraH extraW hEH hEW (maps μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) g
  (invariant μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)
  (ConstructedHolderNoiseAction.constant μE e D atlas openV region hb hb1 F hr hT hbq hg support)
  (action_bound μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap)

theorem core_eq_compact :
    (model μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap
      μ hSlope leaves plus minus radial angle exponent margin lossH lossW hH hW extraH extraW hEH hEW).qa=
    (ConstructedHolderCompactModel.model (Ω:=Space μE e D atlas openV region hb hb1 F hr hT hbq hg support η cap) e D atlas openV region hb hb1 μ hSlope
      leaves plus minus radial angle exponent margin lossH lossW hH hW extraH extraW hEH hEW).qa := rfl
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderNoiseImageModel
