module

public import Mathlib.Analysis.Normed.Module.Complemented
public import Mathlib.Analysis.Complex.Basic

/-! The actual diagonal identity/zero block is precisely the bounded
projection supplied by a topological direct-sum decomposition. -/

public section
open ContinuousLinearMap Submodule
namespace LeanShared.FittingProjection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The diagonal block `(1,0)` conjugates to the actual bounded projection
onto the first topologically complementary subspace. -/
theorem conjugate (K V : Submodule ℂ E) (h : IsTopCompl K V) :
    (K.prodEquivOfIsTopCompl V h).conjContinuousAlgEquiv
      ((1 : K →L[ℂ] K).prodMap (0 : V →L[ℂ] V)) = K.projectionL V h := by
  ext x
  change (((K.prodEquivOfIsTopCompl V h).symm x).1 : E) + 0 = K.projectionL V h x
  rw [prodEquivOfIsTopCompl_symm_apply]
  simp only [add_zero]
  rfl

end LeanShared.FittingProjection
