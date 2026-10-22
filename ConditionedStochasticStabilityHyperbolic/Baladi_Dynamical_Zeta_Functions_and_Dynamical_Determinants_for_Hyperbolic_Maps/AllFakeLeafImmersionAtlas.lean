module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafBorelGeometry
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
public import LeanShared.Geometry.EmbeddedSubmanifoldVolume
public import LeanShared.MeasureTheory.ImmersionAtlasExtraChart

/-! Construct independent intrinsic volume data from the actual embedded
leaf. The graph projection is not used in the volume definition. -/
public noncomputable section
open Set MeasureTheory IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev EmbeddedVolumeAtlas (U : Submodule ℝ E) (Γ : Set E) :=
  EmbeddedSubmanifoldVolume.Data U Γ

def C1Embedded.volumeData {U : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded U Γ) [Nonempty Γ] : EmbeddedVolumeAtlas U Γ :=
  EmbeddedSubmanifoldVolume.data (show EmbeddedSubmanifoldVolume.Embedded U Γ from embedded)

@[expose] def EmbeddedVolumeAtlas.intrinsicMeasure {U : Submodule ℝ E} {Γ : Set E}
    (data : EmbeddedVolumeAtlas U Γ) (μ : Measure U) : Measure Γ :=
  ImmersionAtlasVolume.volume data.model μ
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
