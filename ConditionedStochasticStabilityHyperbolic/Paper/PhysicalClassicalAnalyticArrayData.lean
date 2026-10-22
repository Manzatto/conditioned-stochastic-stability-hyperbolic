module

public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalPrefixSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.EssentialRadiusSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.KellerLiveraniProjectorSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProvedCommonAmbientComparison
public import LeanShared.Geometry.SmoothHolderNormedParents
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierComplete
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarriers
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelStrongParents
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalLayerFrame
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalGlobalApplication
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalStrongFeller
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalNoiseDensity
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularGlobalFiltration
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedGlobalAgreement
public import ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
public import ConditionedStochasticStabilityHyperbolic.Global.LiveFiltrationRealization

/-! Actual heterogeneous analytic models and individual eigencomparison are
constructed from the ordinary physical layer frames. Subordinate strata use
only spectral confinement and comparison, without any mixing requirement. -/

public noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory ProbabilityTheory IsManifold
open scoped Topology NNReal Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalAnalyticArray
open LeanShared Global ShiftedFiltrationGeometry ActualFiltrationGrowth
open PhysicalClassicalLayer KellerLiverani1999 ComplexStrongFeller RestrictedLayerChain
open FiltrationPressureConfinement DyadicCompletion SmoothSupportedManifoldCore
private def operatorEval {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : H) (P : H →L[ℂ] H) : H := P v

universe uM uE
variable {M : Type uM} {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  {ι I : Type*} [Fintype ι] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (A : Set M) (hA : IsOpen A) (Λ : I → Set M) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ) (w : M → ℝ) (R : ℝ) (pressure : I → ℝ)

local instance compactLayer (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

open PhysicalClassicalPrefixSources

variable (frames : ∀ i : Fin ℓ,
  Frame F σ (closedLayer T A Λ ℓ N D i) (layerCompact A Λ ℓ N D i) w R (pressure (D.index i)))

/-- The carrier is a type, rather than the defining submodule object. -/
abbrev strongCarrier (i : Fin ℓ) : Type _ := (frames i).model.strongCarrier
abbrev weakCarrier (i : Fin ℓ) : Type _ := (frames i).model.weakCarrier

local instance strongNormed (i : Fin ℓ) : NormedAddCommGroup (strongCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.strongCarrierNormed
local instance strongSemi (i : Fin ℓ) : SeminormedAddCommGroup (strongCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.strongCarrierSemi
local instance strongScalar (i : Fin ℓ) : NormedSpace ℂ (strongCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.strongCarrierScalar

local instance weakNormed (i : Fin ℓ) : NormedAddCommGroup (weakCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.weakCarrierNormed
local instance weakSemi (i : Fin ℓ) : SeminormedAddCommGroup (weakCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.weakCarrierSemi
local instance weakScalar (i : Fin ℓ) : NormedSpace ℂ (weakCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.weakCarrierScalar

local instance strongUniform (i : Fin ℓ) : UniformSpace (strongCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.strongCarrierUniform
local instance weakUniform (i : Fin ℓ) : UniformSpace (weakCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.weakCarrierUniform

local instance strongTopology (i : Fin ℓ) : TopologicalSpace (strongCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.strongCarrierUniform.toTopologicalSpace
local instance weakTopology (i : Fin ℓ) : TopologicalSpace (weakCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.weakCarrierUniform.toTopologicalSpace

local instance strongComplete (i : Fin ℓ) : CompleteSpace (strongCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.strongCarrierComplete
local instance weakComplete (i : Fin ℓ) : CompleteSpace (weakCarrier F σ A Λ ℓ N D w R pressure frames i) :=
  (frames i).model.weakCarrierComplete

/-- Compactness and both actual averaged operator estimates are outputs. -/
private def produced (L : RegularNoise.Laws (ι := ι)) (i : Fin ℓ) :=
  (frames i).source.model (frames i).exponent (frames i).holder (frames i).model
    (closedLayer T A Λ ℓ N D i) σ F (frames i).representation (frames i).G (frames i).B
    (layerCompact A Λ ℓ N D i) (fun x => w x.val) (frames i).cutoff R L

structure ClassicalOperators where

/-- The universal subordinate-layer source is constructed. -/
def provedClassicalOperators : ClassicalOperators := ⟨⟩

/-- Actual primary Keller–Liverani confinement. -/
theorem ClassicalOperators.confinement (_ : ClassicalOperators) :
  ∀ {H : Type*} {W : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [NormedSpace ℂ W], ClassicalConfinementContract (E := H) (W := W) := classicalConfinementContract

/-- Actual compact-two-norm Fredholm source. -/
theorem ClassicalOperators.essential (_ : ClassicalOperators) :
  ∀ {H : Type*} {W : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W], EssentialRadiusContract (E := H) (W := W) := KellerLiverani1999.essentialRadiusContract

/-- Actual common-core spectral comparison source. -/
theorem ClassicalOperators.comparison (_ : ClassicalOperators) :
  ∀ {H : Type*} {P : Type*} {Z : Type*} {Reg : Type*} {W : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W],
      CommonAmbientClassicalComparison.ClassicalContract
        (A := H) (F := P) (Z := Z) (Reg := Reg) (W := W) := CommonAmbientClassicalComparison.classicalContract

/- Every nonzero eigenvector of the actual original closed-layer operator
is compared with its own actual analytic model. This is derived uniformly
near zero from the ordinary all-z common-ambient theorem, without rank one. -/

end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalAnalyticArray
