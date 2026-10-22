module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderPhysicalModel
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderPhysicalModel

/-! Construction of the physical model from its genuine chart geometry.
Local regular spaces, dense cores, coordinate bounds, smooth block
boundedness and local anisotropic norm bounds are all produced internally. -/
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff SchwartzMap BigOperators BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderPhysicalModel
open LeanShared
variable {E U M J A Ω:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {V S:Set M} (e:J→OpenPartialHomeomorph M E)
  (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)

variable (μ:Measure U) [μ.IsAddHaarMeasure] {slope:ℝ} (hSlope:0≤slope)
  (leaves:D.indices→A→GraphLeafNorm.GraphLeaf U E slope)
  (plus minus:D.indices→Set E) (radial:D.indices→ConeDyadicSymbols.RadialCutoff)
  (angle:∀i,ConeDyadicSymbols.AngularCutoff (plus i) (minus i))
  (exponent:D.indices→Bool→ℝ) (margin:∀i a,exponent i a≤b)

variable (lossH lossW:D.indices→ℝ) (hH:∀i,0<lossH i) (hW:∀i,0<lossW i)
  (extraH extraW:D.indices→Bool→ℝ) (hEH:∀i a,0≤extraH i a) (hEW:∀i a,0≤extraW i a)
  (maps:Ω→M→M) (weight:M→ℝ)
  (invariant:∀a f,FiniteRegularTransferRealization.weightedComposition (maps a) weight
    (view e D openV hb hb1 f)∈(view e D openV hb hb1).range)
  (regularConstant:ℝ)
  (regularBound:∀a f,‖InvariantFiniteRegularTransfer.action
    (view e D openV hb hb1) (view_injective e D openV hb hb1) maps weight invariant a f‖≤regularConstant*‖f‖)


omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem norm_core (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    ‖(model e D atlas openV region hb hb1 μ hSlope leaves plus minus radial angle exponent margin
      lossH lossW hH hW extraH extraW hEH hEW maps weight invariant regularConstant regularBound).qa c‖ =
    ‖ManifoldPhysicalCore.coreMap e D atlas
      (SmoothSupportedManifoldCore.functions V) (SmoothSupportedManifoldCore.smooth V)
      μ hSlope leaves radial angle exponent
      (bounded e D hb hb1 μ hSlope leaves plus minus radial angle exponent margin) c‖ := by
  exact FiniteLocalizationReindex.norm_reindexed
    (B:=fun i:D.indices=>DyadicCompletion.BlockSpace
      (F:=GraphLeafNorm.AmbientFamilySpace μ (leaves i)) (S:=Bool)) e D _

end ConditionedStochasticStabilityHyperbolic.ConstructedHolderPhysicalModel
