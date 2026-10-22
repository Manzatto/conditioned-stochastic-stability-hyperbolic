module
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Tactic.Abel

/-! Moving the source coordinate origin preserves the differential at the
corresponding actual point. Both source and target affine offsets are kept. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates
variable {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_centered_source_change (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F)
    (a c : E) (b : F) (f : E → F) :
    fderiv ℝ (centered L R a b f) (L.symm (c-a)) =
      fderiv ℝ (centered L R c b f) 0 := by
  have shifted : (fun z : P => centered L R a b f (L.symm (c-a)+z)) =
      centered L R c b f := by
    funext z
    dsimp only [centered]
    rw [map_add,L.apply_symm_apply]
    congr 2
    abel_nf
  have derivative := fderiv_comp_add_left (𝕜 := ℝ)
    (f := centered L R a b f) (x := (0 : P)) (L.symm (c-a))
  rw [shifted,add_zero] at derivative
  exact derivative.symm

end LeanShared.CenteredManifoldCoordinates
