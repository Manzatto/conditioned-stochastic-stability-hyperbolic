module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicShooting
public import LeanShared.Geometry.ShootingJacobian
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Differentiation of the literal finite shooting map, along its actual
trajectory. Only differentiability of the original nonlinear steps is used. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] {N : ℕ}

theorem map_differentiableAt (d : Data U S N) (i : Fin N) (z : U × S)
    (h : DifferentiableAt ℝ (d.nonlinear i) z) : DifferentiableAt ℝ (d.map i) z :=
  (((d.expanding i).toContinuousLinearMap.differentiableAt.comp z differentiableAt_fst).add h.fst).prodMk
    (((d.contracting i).differentiableAt.comp z differentiableAt_snd).add h.snd)

theorem evolve_differentiableAt (d : Data U S N) (z : U × S)
    (h : ∀ i : Fin N, DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val))
    (n : ℕ) : DifferentiableAt ℝ (fun w => d.evolve w n) z := by
  induction n with
  | zero => exact differentiableAt_id
  | succ n ih =>
    by_cases before : n < N
    · simpa only [evolve, dite_eq_left before, Function.comp_def] using
        (d.map_differentiableAt ⟨n, before⟩ _ (h ⟨n, before⟩)).comp z ih
    · simpa only [evolve, dite_eq_right before] using ih

theorem shooting_hasFDerivAt (d : Data U S N) (z : U × S)
    (h : ∀ i : Fin N, DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val)) :
    HasFDerivAt d.shooting
      (ShootingJacobian.derivative (fderiv ℝ (fun w => d.evolve w N) z)) z :=
  ShootingJacobian.hasFDerivAt (d.evolve_differentiableAt z h N).hasFDerivAt

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
