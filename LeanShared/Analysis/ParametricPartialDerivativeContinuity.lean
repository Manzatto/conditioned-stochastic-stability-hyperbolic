module
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual state derivatives of a jointly C1 family vary continuously in
both its parameter and state. No parameter regularity of separate derivative
fields is supplied. -/
public section
namespace LeanShared.ParametricPartialDerivativeContinuity
open scoped ContDiff

theorem continuousAt
    {A E F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : A × E → F) (p : A × E) (smooth : ContDiffAt ℝ 1 f p) :
    ContinuousAt (fun q : A × E => fderiv ℝ (fun y => f (q.1,y)) q.2) p := by
  have duplicated : ContDiffAt ℝ 1 (fun q : (A × E) × E => f (q.1.1,q.2)) (p,p.2) :=
    smooth.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (duplicated.fderiv (m := 0) contDiffAt_snd (by simp)).continuousAt

end LeanShared.ParametricPartialDerivativeContinuity
