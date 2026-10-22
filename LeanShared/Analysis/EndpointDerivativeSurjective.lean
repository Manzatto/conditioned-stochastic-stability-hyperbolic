module
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Full control rank gives full rank of the joint state/endpoint map. -/
public section
namespace LeanShared.SubmersionLinearCoordinates

theorem endpoint_fderiv_surjective
    {X A Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : X × A → Y} {x : X} {a : A}
    (differentiable : DifferentiableAt ℝ f (x, a))
    (rank : Function.Surjective (fderiv ℝ (fun b => f (x, b)) a)) :
    Function.Surjective (fderiv ℝ (fun z : X × A => (z.1, f z)) (x, a)) := by
  have control := (differentiable.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x a)).fderiv
  have endpoint := hasFDerivAt_fst.prodMk differentiable.hasFDerivAt
  rw [endpoint.fderiv]
  intro y
  obtain ⟨b, hb⟩ := rank (y.2 - fderiv ℝ f (x, a) (y.1, 0))
  change (fderiv ℝ (f ∘ Prod.mk x) a) b = _ at hb
  rw [control] at hb
  refine ⟨(y.1, b), Prod.ext rfl ?_⟩
  change fderiv ℝ f (x, a) (y.1, b) = y.2
  have split : (y.1, b) = (y.1, (0 : A)) + ((0 : X), b) := by simp
  rw [split, map_add]
  change fderiv ℝ f (x, a) (y.1, 0) +
    (fderiv ℝ f (x, a)).comp (ContinuousLinearMap.inr ℝ X A) b = y.2
  rw [hb, add_comm, sub_add_cancel]

end LeanShared.SubmersionLinearCoordinates
