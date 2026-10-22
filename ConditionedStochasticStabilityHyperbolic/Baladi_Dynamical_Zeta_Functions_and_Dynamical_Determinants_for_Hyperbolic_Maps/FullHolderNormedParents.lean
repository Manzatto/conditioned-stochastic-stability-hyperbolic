module

public import LeanShared.Geometry.SmoothHolderNormedParents

public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.FullHolderNormedParents
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [CompactSpace M]
  (u : ℝ) (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)

@[expose, instance_reducible] def normed :
    NormedAddCommGroup (SmoothHolderTestSpaces.space u holder (univ : Set M)) := inferInstance

@[expose, instance_reducible] def seminormed :
    SeminormedAddCommGroup (SmoothHolderTestSpaces.space u holder (univ : Set M)) :=
  (normed u holder).toSeminormedAddCommGroup

local instance cachedNormed : NormedAddCommGroup
    (SmoothHolderTestSpaces.space u holder (univ : Set M)) := normed u holder
local instance cachedSemi : SeminormedAddCommGroup
    (SmoothHolderTestSpaces.space u holder (univ : Set M)) := seminormed u holder

@[expose, instance_reducible] def scalar :
    NormedSpace ℂ (SmoothHolderTestSpaces.space u holder (univ : Set M)) := inferInstance

end ConditionedStochasticStabilityHyperbolic.FullHolderNormedParents
