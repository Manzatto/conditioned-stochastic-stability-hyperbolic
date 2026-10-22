module

public import LeanShared.Geometry.LinearRechartedAtlas

/-! The actual identity map is a smooth diffeomorphism between the old
model and its constructed linear recharting. This lets rank and joint C¹
properties transport by the genuine chain rule. -/

@[expose] public noncomputable section
open Set IsManifold Filter
open scoped Manifold ContDiff Topology
namespace LeanShared.LinearRechartedManifold

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  (e : E ≃L[ℝ] F)

theorem identity_forward : letI := charts (M := M) e;
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ (@id M) := by
  let := charts (M := M) e
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  let c := chartAt E x
  have ht : c.target ∈ 𝓝 (c x) := c.open_target.mem_nhds (mem_chart_target E x)
  have hg : (fun y : E => e (c (c.symm y))) =ᶠ[𝓝 (c x)] e := by
    filter_upwards [ht] with y hy
    rw [c.right_inv hy]
  have hh : ContDiffAt ℝ ∞ (fun y : E => e (c (c.symm y))) (c x) :=
    e.contDiff.contDiffAt.congr_of_eventuallyEq hg
  exact hh.contDiffWithinAt

theorem identity_backward : letI := charts (M := M) e;
    ContMDiff (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ (@id M) := by
  let := charts (M := M) e
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_id, ?_⟩
  let c := chartAt E x
  have ht : e.symm ⁻¹' c.target ∈ 𝓝 (e (c x)) :=
    (c.open_target.preimage e.symm.continuous).mem_nhds (by
      simp only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
      exact mem_chart_target E x)
  have hg : (fun y : F => c (c.symm (e.symm y))) =ᶠ[𝓝 (e (c x))] e.symm := by
    filter_upwards [ht] with y hy
    exact c.right_inv hy
  have hh : ContDiffAt ℝ ∞ (fun y : F => c (c.symm (e.symm y))) (e (c x)) :=
    e.symm.contDiff.contDiffAt.congr_of_eventuallyEq hg
  exact hh.contDiffWithinAt

/-- No points or maps are changed; only the linear coordinate model is. -/
def identityDiffeomorph : letI := charts (M := M) e; M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, F)⟯ M := by
  letI := charts (M := M) e
  exact {
  toEquiv := Equiv.refl M
  contMDiff_toFun := identity_forward e
  contMDiff_invFun := identity_backward e }

end LeanShared.LinearRechartedManifold
