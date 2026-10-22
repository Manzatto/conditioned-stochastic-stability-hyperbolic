module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalManifoldModel
public import LeanShared.Geometry.ManifoldClosedHolderLocalization
public import LeanShared.Geometry.FiniteLocalizationReindex
public import LeanShared.Analysis.CompactSchwartzHolderBlocks

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

abbrev Regular := ManifoldSmoothHolderCore.Lower e D openV hb hb1
abbrev Local (i:D.indices) := ManifoldClosedHolderLocalization.Local e D hb hb1 i
local instance regularNormed : NormedAddCommGroup (Regular e D openV hb hb1) := inferInstance
local instance regularSemi : SeminormedAddCommGroup (Regular e D openV hb hb1) :=
  (regularNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance regularScalar : NormedSpace ℂ (Regular e D openV hb hb1) := inferInstance
local instance localNormed (i:D.indices) : NormedAddCommGroup (Local e D hb hb1 i) := inferInstance
local instance localSemi (i:D.indices) : SeminormedAddCommGroup (Local e D hb hb1 i) :=
  (localNormed e D hb hb1 i).toSeminormedAddCommGroup
local instance localScalar (i:D.indices) : NormedSpace ℂ (Local e D hb hb1 i) := inferInstance
local instance localComplete (i:D.indices) : CompleteSpace (Local e D hb hb1 i) := inferInstance

@[expose] def view : Regular e D openV hb hb1 →ₗ[ℂ](M→ℂ) where
  toFun f := fun x=>ManifoldSmoothHolderCore.physical e D openV hb hb1 f x
  map_add' f g := by ext x;exact congrArg (fun z:M→ᵇℂ=>z x) (map_add _ f g)
  map_smul' z f := by ext x;exact congrArg (fun z:M→ᵇℂ=>z x) (map_smul _ z f)

omit [MeasurableSpace E] [BorelSpace E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem view_injective : Function.Injective (view e D openV hb hb1) := by
  intro f g equal
  apply ManifoldHolderQuotient.physical_injective
  ext x
  exact congrFun equal x

@[expose] def localView (i:D.indices) : Local e D hb hb1 i →ₗ[ℂ](E→ℂ) where
  toFun f := fun x=>EuclideanSmoothHolderCore.physical
    (ConstructedManifoldLocalization.support_compact e D i).closure hb hb1 f x
  map_add' f g := by ext x;exact congrArg (fun z:E→ᵇℂ=>z x) (map_add _ f g)
  map_smul' z f := by ext x;exact congrArg (fun z:E→ᵇℂ=>z x) (map_smul _ z f)

omit [MeasurableSpace E] [BorelSpace E] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem localView_injective (i:D.indices) : Function.Injective (localView e D hb hb1 i) := by
  intro f g equal
  apply EuclideanSmoothHolderCore.physical_injective
  ext x
  exact congrFun equal x

variable (μ:Measure U) [μ.IsAddHaarMeasure] {slope:ℝ} (hSlope:0≤slope)
  (leaves:D.indices→A→GraphLeafNorm.GraphLeaf U E slope)
  (plus minus:D.indices→Set E) (radial:D.indices→ConeDyadicSymbols.RadialCutoff)
  (angle:∀i,ConeDyadicSymbols.AngularCutoff (plus i) (minus i))
  (exponent:D.indices→Bool→ℝ) (margin:∀i a,exponent i a≤b)

include hb hb1 margin in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem bounded (i:D.indices) : SchwartzAmbientBlocks.SmoothCoreBounded μ hSlope (leaves i)
    (ConstructedManifoldLocalization.support e D i)
    (ConeDyadicSymbols.symbols (radial i) (angle i)) (exponent i) :=
  CompactSchwartzHolderBlocks.bounded μ hSlope (leaves i) (radial i) (angle i)
    (ConstructedManifoldLocalization.support_compact e D i) hb hb1 (exponent i) (margin i)

@[expose] def blockConstant (i:D.indices) : ℝ := Classical.choose
  (CompactSchwartzHolderBlocks.bound μ hSlope (leaves i) (radial i) (angle i)
    (ConstructedManifoldLocalization.support_compact e D i) hb hb1 (exponent i) (margin i))

@[expose] def coordinateConstant (i:D.indices) : ℝ := Classical.choose
  (ManifoldClosedHolderLocalization.bound e D atlas openV hb hb1 region i)

variable (lossH lossW:D.indices→ℝ) (hH:∀i,0<lossH i) (hW:∀i,0<lossW i)
  (extraH extraW:D.indices→Bool→ℝ) (hEH:∀i a,0≤extraH i a) (hEW:∀i a,0≤extraW i a)
  (maps:Ω→M→M) (weight:M→ℝ)
  (invariant:∀a f,FiniteRegularTransferRealization.weightedComposition (maps a) weight
    (view e D openV hb hb1 f)∈(view e D openV hb hb1).range)
  (regularConstant:ℝ)
  (regularBound:∀a f,‖InvariantFiniteRegularTransfer.action
    (view e D openV hb hb1) (view_injective e D openV hb hb1) maps weight invariant a f‖≤regularConstant*‖f‖)

@[expose] def model : PhysicalManifoldModel.Data (E:=E) (U:=U) (M:=M)
    (AtlasIndex:=D.indices) (Reg:=Regular e D openV hb hb1) (LocalReg:=fun i=>↥(Local e D hb hb1 i))
    (A:=A) (Ω:=Ω) V S μ where
  atlas := FiniteLocalizationReindex.atlas e D
  localization := FiniteLocalizationReindex.data e D
  atlas_mem j := atlas j.val
  region_subset_support := region
  view := view e D openV hb hb1
  view_injective := view_injective e D openV hb hb1
  regularCore := ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1
  regularCore_dense := ManifoldSmoothHolderCore.smooth_dense e D atlas openV hb hb1 region
  view_core c := by ext x;exact ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region c x
  evaluate x := (BoundedContinuousFunction.evalCLM ℂ x).comp (ManifoldSmoothHolderCore.physical e D openV hb hb1)
  evaluation _ _ := rfl
  localView i := localView e D hb hb1 i.val
  localView_injective i := localView_injective e D hb hb1 i.val
  localCore i := CompactSchwartzHolderCore.core (ConstructedManifoldLocalization.support_compact e D i.val) hb hb1
  localCore_dense i := CompactSchwartzHolderCore.core_dense (ConstructedManifoldLocalization.support_compact e D i.val) hb hb1
  localView_core _ _ := rfl
  localEvaluate i x := (BoundedContinuousFunction.evalCLM ℂ x).comp
    (EuclideanSmoothHolderCore.physical (ConstructedManifoldLocalization.support_compact e D i.val).closure hb hb1)
  localEvaluation _ _ _ := rfl
  coordinateConstant i := coordinateConstant e D atlas openV region hb hb1 i.val
  coordinateBound i c := Classical.choose_spec
    (ManifoldClosedHolderLocalization.bound e D atlas openV hb hb1 region i.val) c
  slope := slope
  slope_nonnegative := hSlope
  leaves i := leaves i.val
  conePlus i := plus i.val
  coneMinus i := minus i.val
  radial i := radial i.val
  angle i := angle i.val
  exponent i := exponent i.val
  boundedBlocks i := bounded e D hb hb1 μ hSlope leaves plus minus radial angle exponent margin i.val
  lossH i := lossH i.val
  lossW i := lossW i.val
  lossH_positive i := hH i.val
  lossW_positive i := hW i.val
  extraH i := extraH i.val
  extraW i := extraW i.val
  extraH_nonnegative i := hEH i.val
  extraW_nonnegative i := hEW i.val
  blockConstant i := blockConstant e D hb hb1 μ hSlope leaves plus minus radial angle exponent margin i.val
  blockBound i f := (Classical.choose_spec (CompactSchwartzHolderBlocks.bound μ hSlope
    (leaves i.val) (radial i.val) (angle i.val)
    (ConstructedManifoldLocalization.support_compact e D i.val) hb hb1 (exponent i.val) (margin i.val))).2 _ f
  maps := maps
  weight := weight
  invariant := invariant
  coreRegular a c := by
    have h := invariant a (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)
    have eqn : view e D openV hb hb1 (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c)=
        SmoothSupportedManifoldCore.functions V c := by
      ext x
      exact ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region c x
    exact eqn ▸ h
  regularConstant := regularConstant
  regularBound := regularBound
end ConditionedStochasticStabilityHyperbolic.ConstructedHolderPhysicalModel
