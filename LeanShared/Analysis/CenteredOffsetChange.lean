module
public import LeanShared.Geometry.CenteredManifoldCoordinates
public import Mathlib.Tactic.Abel

/-! Changing the reference target offset changes a centered map only by a
constant. Its derivative and every perturbation difference are unchanged. -/
public noncomputable section
namespace LeanShared.CenteredManifoldCoordinates

variable {P Q E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem fderiv_centered_offset (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b c : F)
    (f : E → F) (z : P) :
    fderiv ℝ (centered L R a b f) z = fderiv ℝ (centered L R a c f) z := by
  change fderiv ℝ (fun v => R.symm (f (a + L v) - b)) z =
    fderiv ℝ (fun v => R.symm (f (a + L v) - c)) z
  simp only [map_sub,fderiv_sub_const]

 theorem differentiableAt_centered_offset (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b c : F)
    (f : E → F) (z : P) (smooth : DifferentiableAt ℝ (centered L R a b f) z) :
    DifferentiableAt ℝ (centered L R a c f) z := by
  change DifferentiableAt ℝ (fun v => R.symm (f (a + L v) - b)) z at smooth
  have raw := smooth.add_const (R.symm b)
  have differentiable : DifferentiableAt ℝ (fun v => R.symm (f (a + L v))) z := by
    simpa only [centered,map_sub,sub_add_cancel] using raw
  change DifferentiableAt ℝ (fun v => R.symm (f (a + L v) - c)) z
  simpa only [map_sub] using differentiable.sub_const (R.symm c)

 theorem centered_noise_difference_zero (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] F) (a : E) (b : F)
    (f g : E → F) :
    centered L R a b f 0 - centered L R a b g 0 = centered L R a (g a) f 0 := by
  simp only [centered,_root_.map_zero,add_zero,map_sub]
  abel

end LeanShared.CenteredManifoldCoordinates
