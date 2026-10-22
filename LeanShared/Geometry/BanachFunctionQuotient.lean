module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
/-! Quotient a Banach function generator by its actual closed kernel.
Completeness and the faithful continuous function realization are proved
from the continuous generator; no injective realization source is used. -/
public noncomputable section
open scoped BoundedContinuousFunction
namespace LeanShared.BanachFunctionQuotient
variable {𝕜 H X F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace X]
  (T : H →L[𝕜] (X →ᵇ F))
instance kernel_closed : IsClosed (T.ker : Set H) := T.isClosed_ker
@[expose] def Space := H ⧸ T.ker
instance spaceNormed : NormedAddCommGroup (Space T) := by unfold Space; infer_instance
instance spaceScalar : NormedSpace 𝕜 (Space T) := by unfold Space; infer_instance
instance complete [CompleteSpace H] : CompleteSpace (Space T) := by unfold Space; infer_instance
@[expose] def quotient : H →L[𝕜] Space T := T.ker.mkQL
@[expose] def physical : Space T →L[𝕜] (X →ᵇ F) := T.ker.liftQL T le_rfl
theorem quotient_surjective : Function.Surjective (quotient T) := Submodule.mkQ_surjective _
theorem physical_quotient (h : H) : physical T (quotient T h) = T h := rfl
theorem physical_injective : Function.Injective (physical T) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
end LeanShared.BanachFunctionQuotient
