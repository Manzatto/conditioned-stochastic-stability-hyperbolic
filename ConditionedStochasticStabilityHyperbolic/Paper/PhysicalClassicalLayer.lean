module

public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderAnnealedConjugation
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.LayerNoiseClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedLayerModel
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedAllScaleMaps
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularLayerNoiseSources
public import LeanShared.Analysis.CommonAmbientGlobalTests

/-! Ordinary cited anisotropic facts over the actual supported/full little
Hölder spaces. All regular realizations, dense cores, test inclusions and
physical compatibility identities are constructed, not source fields. -/

public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
open LeanShared DyadicCompletion SmoothSupportedManifoldCore

variable {E U M AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [T2Space M] [CompactSpace M]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]

variable (u : ℝ)
  (holder : ∀ c : core (E := E) (univ : Set M), ∃ C : ℝ,
    ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

abbrev Regular (V : Set M) := PhysicalHolderClassicalSources.Regular u holder V
abbrev FullTest := PhysicalHolderClassicalSources.FullTest u holder

local instance fullSemi : SeminormedAddCommGroup (FullTest u holder) :=
  (inferInstance : NormedAddCommGroup (FullTest u holder)).toSeminormedAddCommGroup
local instance supportedSemi (V : Set M) : SeminormedAddCommGroup (Regular u holder V) :=
  (inferInstance : NormedAddCommGroup (Regular u holder V)).toSeminormedAddCommGroup
local instance fullDualGroup : NormedAddCommGroup (FullTest u holder →L[ℂ] ℂ) := inferInstance
local instance fullDualSpace : NormedSpace ℂ (FullTest u holder →L[ℂ] ℂ) := inferInstance
local instance supportedDualGroup (V : Set M) :
    NormedAddCommGroup (Regular u holder V →L[ℂ] ℂ) := inferInstance
local instance supportedDualSpace (V : Set M) :
    NormedSpace ℂ (Regular u holder V →L[ℂ] ℂ) := inferInstance

variable {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : PhysicalManifoldModel.Data (E := E) (U := U) (M := M)
    (AtlasIndex := AtlasIndex) (Reg := Regular u holder V) (LocalReg := LocalReg)
    (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]


open KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
variable [MetricSpace Ω]


variable {ι : Type*} [Fintype ι] {T : M ≃ₜ M} {rNoise : ℝ}
    (F : RegularNoise.Maps (E := E) (ι := ι) T rNoise)
    (p : RegularNoise.Representation F Ω m.maps)
    {Fiber : M → Type*} [∀ x, NormedAddCommGroup (Fiber x)]
    [∀ x, InnerProductSpace ℝ (Fiber x)] [∀ x, FiniteDimensional ℝ (Fiber x)]
    {Params : Type*} {I : ℕ → Type*} {Order : Type*} [Fintype Order]
    (G B : Set M) (hK : IsCompact K) (w wc : K → ℝ) (R : ℝ)

/-- Ordinary classical facts for one literal retained stratum. This source is
independent of the random law: no analytic input bundle, compactness,
comparison, noisy spectral gap, QEM or weak limit is a field. Stable dimension
and chart regular spaces may vary between separate instances. -/
structure Data where
  primitive : PhysicalManifoldPrimitiveSources.Data m
    (Fiber := Fiber) (Params := Params) (I := I) (Order := Order)
  reference : primitive.pressure.T = p.reference
  weakRate : ℝ
  principal_positive : 0 < primitive.pressure.ρ
  principal_lt_weak : primitive.pressure.ρ < weakRate
  weak_oneStep : primitive.rows.weakBound ≤ weakRate
  scale_ge_one : 1 ≤ R
  principal_lt_scale : primitive.pressure.ρ < R
  common : PhysicalHolderClassicalSources.Data u holder m K (σ.comap Subtype.val)
  noise : RegularLayerNoiseSources.Data p σ V K G B hK w wc R
    (fullView u holder) (fullView_injective u holder) (fullCore u holder)
  submersion : RegularNoise.ControlSubmersionSources (E := E) (ι := ι) σ
  weight_continuous : Continuous w
  cutoff_measurable : Measurable wc
  weight_bound : ∀ x, w x ≤ R
  cutoff_bound : ∀ x, wc x ≤ R
  model_weight : ∀ x : K, m.weight x.val = wc x
  realCutoff : ∀ i x, star (m.localization.cutoff i x) = m.localization.cutoff i x
  evenAngle : ∀ i ξ, (m.angle i).toFun (-ξ) = (m.angle i).toFun ξ
  regularR : ℝ
  regularT : ℝ
  regularS : ℝ
  margins : RegularCoreApproximation.RegularityMargins regularR regularT regularS u

namespace Data
variable (d : Data u holder m K σ F p (Fiber := Fiber) (Params := Params) (I := I)
  (Order := Order) G B hK w wc R)

/-- The ordinary Whitney representation supplies the complete actual noise
parameter family; its robust analytic estimates are then proved internally. -/
@[expose] def modelSource : PhysicalLayerModels.Data m (Fiber := Fiber) (Params := Params)
    (I := I) (Order := Order) (Noise := RegularNoise.FixedControl (ι := ι)) R :=
  RepresentedLayerModel.source m F p d.primitive d.reference d.weakRate R
    d.principal_positive d.principal_lt_weak d.weak_oneStep d.scale_ge_one d.principal_lt_scale

/-- Actual compact embeddings, pressure bounds, noise measurability and KL
inputs are outputs of the physical model constructor. -/
def model (L : RegularNoise.Laws (ι := ι)) := (d.modelSource u holder m K σ F p G B hK w wc R).produce m L.fixedLaw

/-- Smoothing and the independent inverse-density/plaque certificate follow
from the actual regular noise and its ordinary rank/volume/Jacobian sources. -/
def noiseSources (L : RegularNoise.Laws (ι := ι)) :=
  d.noise.produce d.submersion L d.weight_continuous d.cutoff_measurable
    (zero_lt_one.trans_le d.scale_ge_one) d.weight_bound d.cutoff_bound p.allScale_measurable

end Data
end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayer
