module
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! Exact first-derivative operator norm comparisons from the ordinary
iterated-derivative norm. This connects a literal Whitney certificate to the
linear operator bounds used by the local graph transform. -/
public section
namespace LeanShared.FirstDerivativeDifferenceNorm

theorem norm_sub_eq {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f g : E → F) (x : E) :
    ‖fderiv 𝕜 f x - fderiv 𝕜 g x‖ =
      ‖iteratedFDeriv 𝕜 1 f x - iteratedFDeriv 𝕜 1 g x‖ := by
  let e := continuousMultilinearCurryFin1 𝕜 E F
  have image (h : E → F) : e (iteratedFDeriv 𝕜 1 h x) = fderiv 𝕜 h x := by
    ext v
    simp only [e, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply, Fin.snoc_zero]
  calc
    _ = ‖e (iteratedFDeriv 𝕜 1 f x) - e (iteratedFDeriv 𝕜 1 g x)‖ := by rw [image, image]
    _ = ‖e (iteratedFDeriv 𝕜 1 f x - iteratedFDeriv 𝕜 1 g x)‖ := by rw [map_sub]
    _ = _ := e.norm_map _

end LeanShared.FirstDerivativeDifferenceNorm
