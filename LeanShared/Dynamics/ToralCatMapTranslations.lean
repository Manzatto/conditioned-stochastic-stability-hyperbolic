module

public import LeanShared.Dynamics.ToralCatMapAffineCharts
public import LeanShared.Geometry.SmoothMapFractionalRegularity

/-! The concrete two-control translation perturbations of the cat map.
The family is jointly smooth, its actual control derivative is surjective,
and its uniform displacement is bounded by the control norm. -/

set_option maxHeartbeats 800000
@[expose] public noncomputable section
open Set IsManifold Bundle Function
open scoped Manifold ContDiff Bundle Topology
namespace LeanShared.ToralCatMap

abbrev Control := Fin 2 → ℝ

def controlEquivalence : Control ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

def perturbation (u : Control) (x : Torus) : Torus := quotient (controlEquivalence u) + map x

theorem smooth_first : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞
    (@Prod.fst UnitAddCircle UnitAddCircle) := by
  have old : ContMDiff (𝓘(ℝ, ProductModel)) (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞
      (@Prod.fst UnitAddCircle UnitAddCircle) := by
    simpa only [modelWithCornersSelf_prod] using contMDiff_fst
  exact old.comp identity_from_hilbert

theorem smooth_second : ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞
    (@Prod.snd UnitAddCircle UnitAddCircle) := by
  have old : ContMDiff (𝓘(ℝ, ProductModel)) (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞
      (@Prod.snd UnitAddCircle UnitAddCircle) := by
    simpa only [modelWithCornersSelf_prod] using contMDiff_snd
  exact old.comp identity_from_hilbert

theorem smooth_perturbation :
    ContMDiff ((𝓘(ℝ, Control)).prod (𝓘(ℝ, HilbertModel))) (𝓘(ℝ, HilbertModel)) ∞
      (fun p : Control × Torus => perturbation p.1 p.2) := by
  have ctrl (i : Fin 2) : ContMDiff ((𝓘(ℝ, Control)).prod (𝓘(ℝ, HilbertModel)))
      (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞ (fun p : Control × Torus => (p.1 i : UnitAddCircle)) :=
    UnitAddCircleManifold.smooth_projection.comp
      ((ContinuousLinearMap.proj i : Control →L[ℝ] ℝ).contDiff.contMDiff.comp contMDiff_fst)
  have first : ContMDiff ((𝓘(ℝ, Control)).prod (𝓘(ℝ, HilbertModel)))
      (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞ (fun p : Control × Torus => (map p.2).1) :=
    smooth_first.comp (smooth_map.comp contMDiff_snd)
  have second : ContMDiff ((𝓘(ℝ, Control)).prod (𝓘(ℝ, HilbertModel)))
      (𝓘(ℝ, UnitAddCircleManifold.Model)) ∞ (fun p : Control × Torus => (map p.2).2) :=
    smooth_second.comp (smooth_map.comp contMDiff_snd)
  have product : ContMDiff ((𝓘(ℝ, Control)).prod (𝓘(ℝ, HilbertModel))) (𝓘(ℝ, ProductModel)) ∞
      (fun p : Control × Torus => perturbation p.1 p.2) := by
    rw [modelWithCornersSelf_prod (E := UnitAddCircleManifold.Model) (F := UnitAddCircleManifold.Model)]
    exact ((ctrl 0).add first).prodMk ((ctrl 1).add second)
  exact identity_to_hilbert.comp product

theorem smooth_perturbation_fixed (u : Control) :
    ContMDiff (𝓘(ℝ, HilbertModel)) (𝓘(ℝ, HilbertModel)) ∞ (perturbation u) :=
  smooth_perturbation.comp (contMDiff_const.prodMk contMDiff_id)

theorem perturbation_zero (x : Torus) : perturbation 0 x = homeomorph x := by
  change (0 : Torus) + map x = map x
  exact zero_add _

theorem perturbation_uniform (u : Control) (x : Torus) :
    dist (perturbation u x) (homeomorph x) ≤ ‖u‖ := by
  change dist (quotient (controlEquivalence u) + map x) (map x) ≤ ‖u‖
  rw [dist_eq_norm, add_sub_cancel_right]
  change max ‖(u 0 : UnitAddCircle)‖ ‖(u 1 : UnitAddCircle)‖ ≤ ‖u‖
  exact max_le ((QuotientAddGroup.norm_mk_le_norm (m := u 0)).trans (norm_le_pi_norm u 0))
    ((QuotientAddGroup.norm_mk_le_norm (m := u 1)).trans (norm_le_pi_norm u 1))

set_option backward.isDefEq.respectTransparency false in
theorem perturbation_control_surjective (u : Control) (x : Torus) :
    Function.Surjective (mfderiv (𝓘(ℝ, Control)) (𝓘(ℝ, HilbertModel))
      (fun v => perturbation v x) u) := by
  obtain ⟨z, rfl⟩ := quotient_surjective x
  let F : Control → (ℝ × ℝ) := fun v => controlEquivalence v + map z
  have same : (fun v => perturbation v (quotient z)) = quotient ∘ F := by
    funext v
    ext <;> simp [perturbation, F, quotient, controlEquivalence, map]
  have derivative : HasFDerivAt F controlEquivalence.toContinuousLinearMap u :=
    controlEquivalence.toContinuousLinearMap.hasFDerivAt.add_const (map z)
  rw [same, mfderiv_comp u ((smooth_quotient.mdifferentiable (by simp)) _) derivative.differentiableAt.mdifferentiableAt,
    derivative.hasMFDerivAt.mfderiv]
  exact (quotientDifferential_bijective (F u)).2.comp controlEquivalence.surjective

end LeanShared.ToralCatMap
