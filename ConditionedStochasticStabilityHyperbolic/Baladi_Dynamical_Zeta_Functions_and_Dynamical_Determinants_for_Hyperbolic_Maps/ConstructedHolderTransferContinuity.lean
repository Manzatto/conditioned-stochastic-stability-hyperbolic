module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.ConstructedHolderTransferInterpolation
public import LeanShared.Geometry.ManifoldHolderFamilyInterpolation
public import LeanShared.Analysis.FiniteRegularCoreNoiseContinuity

/-! Actual weighted transfers of smooth inputs satisfy power interpolation
once their higher Holder operator norms are uniformly bounded. The same
physical weighted composition is used at both orders. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ConstructedHolderTransferContinuity
open LeanShared ConstructedHolderPhysicalModel ConstructedHolderSingleTransfer
open ConstructedHolderTransferInterpolation
variable {E M J A:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μE:Measure E) [μE.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀j,e j∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (openV:IsOpen V) (region:V⊆S) {b:ℝ} (hb:0<b) (hb1:b<1)
  {g:M→ℝ} {q a:ℝ} (hbq:b<q)
  (hg:FractionalManifoldRegularity.Regular (E:=E) (F:=ℝ) q g)
  (support:tsupport g⊆V)
  (ha:0<a) (ha1:a<1) (hab:b<a) (haq:a<q)
  (maps:A→M→M) (regular:∀p,ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (maps p))

variable [TopologicalSpace A]
include μE atlas region hbq hg support ha ha1 hab haq maps regular in
theorem continuous_action {B:ℝ} (hB:0≤B)
    (bound:∀p,‖transfer μE e D atlas openV region ha ha1 (maps p) (regular p) haq hg support‖≤B)
    (joint:Continuous (fun z:A×M=>maps z.1 z.2))
    (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    Continuous (fun p=>action μE e D atlas openV region hb hb1 hbq hg support maps regular p c) := by
  obtain ⟨K,_,estimate⟩:=exists_power_bound μE e D atlas openV region hb hb1 hbq hg support
    ha ha1 hab haq maps regular hB bound c
  apply FiniteRegularCoreNoiseContinuity.continuous_regularFunction_of_interpolation
    maps g c.val joint hg.differentiable.continuous c.property.1.continuous
    Set.univ isCompact_univ (by simp) (Regular e D openV hb hb1)
    (view e D openV hb hb1)
    (fun p=>action μE e D atlas openV region hb hb1 hbq hg support maps regular p c)
    ?_ ((a-b)/a) (div_pos (sub_pos.mpr hab) ha) (fun _=>K) ?_
  · intro p x
    change view e D openV hb hb1
      (transfer μE e D atlas openV region hb hb1 (maps p) (regular p) hbq hg support
        (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)) x=_
    rw [transfer_function]
    change (g x:ℂ)*ManifoldSmoothHolderCore.physical e D openV hb hb1
      (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c) (maps p x)=_
    rw [ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region]
    rfl
  · intro p t ε hε error
    exact estimate t p ε hε error
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderTransferContinuity
