module
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-! Continuity of inverse frame families between two fixed model spaces.
Only the forward operator family is assumed continuous. -/
public noncomputable section
open scoped Topology
namespace LeanShared.ContinuousLinearFrameInverse
variable {X P E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_inverse (f : X → P ≃L[ℝ] E)
    (forward : Continuous (fun x => (f x).toContinuousLinearMap)) :
    Continuous (fun x => (f x).symm.toContinuousLinearMap) := by
  rw [continuous_iff_continuousAt]
  intro x
  let e := f x
  let normalized := fun y => e.symm.toContinuousLinearMap.comp (f y).toContinuousLinearMap
  have cn : Continuous normalized := forward.const_clm_comp e.symm.toContinuousLinearMap
  have atCenter : normalized x = (1 : P →L[ℝ] P) := by
    ext v
    exact e.symm_apply_apply v
  have inverseAt : ContinuousAt Ring.inverse (normalized x) := by
    rw [atCenter]
    exact NormedRing.inverse_continuousAt (R := P →L[ℝ] P) (1 : (P →L[ℝ] P)ˣ)
  have normalizedInverse := inverseAt.comp cn.continuousAt
  let post : (P →L[ℝ] P) →L[ℝ] (E →L[ℝ] P) :=
    (ContinuousLinearMap.compL ℝ E P P).flip e.symm.toContinuousLinearMap
  have result := post.continuous.continuousAt.comp normalizedInverse
  convert result using 1
  funext y
  change (f y).symm.toContinuousLinearMap =
    (Ring.inverse (e.symm.toContinuousLinearMap.comp (f y).toContinuousLinearMap)).comp
      e.symm.toContinuousLinearMap
  rw [← ContinuousLinearMap.inverse_equiv, ContinuousLinearMap.inverse_eq_ringInverse e]

end LeanShared.ContinuousLinearFrameInverse
