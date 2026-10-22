module
public import LeanShared.Analysis.SubmersionLinearCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Topology.Algebra.Module.Determinant

/-! Finite-dimensional surjective differentials remain surjective nearby.
This supplies genuine full-rank neighborhoods at boundary controls. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Filter
open scoped Topology

theorem eventually_surjective
    {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace T] {D : T → E →L[ℝ] F} {t : T}
    (continuousD : ContinuousAt D t) (rank : Function.Surjective (D t)) :
    ∀ᶠ z in 𝓝 t, Function.Surjective (D z) := by
  obtain ⟨r, right⟩ := (D t).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr rank)
  let rC : F →L[ℝ] E := r.toContinuousLinearMap
  have identity : (D t).comp rC = ContinuousLinearMap.id ℝ F := by
    ext y
    exact congrArg (fun L : F →ₗ[ℝ] F => L y) right
  have continuousDet : ContinuousAt (fun z => ((D z).comp rC).det) t :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (continuousD.clm_comp continuousAt_const)
  have nonzero : ((D t).comp rC).det ≠ 0 := by
    rw [identity]
    change (LinearMap.id : F →ₗ[ℝ] F).det ≠ 0
    rw [LinearMap.det_id]
    exact one_ne_zero
  filter_upwards [continuousDet.eventually_ne nonzero] with z hz
  let e := ((D z).comp rC).toContinuousLinearEquivOfDetNeZero hz
  intro y
  obtain ⟨v, hv⟩ := e.surjective y
  refine ⟨rC v, ?_⟩
  exact hv

end LeanShared.SubmersionLinearCoordinates
