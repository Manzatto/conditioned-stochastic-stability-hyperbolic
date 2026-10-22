module
public import LeanShared.Geometry.DiffeomorphismChartDerivative
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! The Jacobian of an actual smooth chart transition is nonzero, including
in dimension zero. The derivative equivalence is constructed from ordinary
chart calculus. -/
public noncomputable section
namespace LeanShared.ChartTransitionJacobian
open Set IsManifold
open scoped Manifold ContDiff

theorem inverse_hasFDerivAt
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (e d : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (inside : y ∈ (e.symm.trans d).target) :
    ∃ L : E ≃L[ℝ] E, HasFDerivAt (e.symm.trans d).symm L.toContinuousLinearMap y := by
  have eDiff : e.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have dDiff : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hd).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hd).mdifferentiableOn (by simp)⟩
  obtain ⟨L,derivative⟩ := DiffeomorphismChartDerivative.exists_equivalence (Homeomorph.refl M)
    mdifferentiable_id mdifferentiable_id d e dDiff eDiff (d.symm y) (d.map_target inside.1) inside.2
  refine ⟨L,?_⟩
  simpa only [OpenPartialHomeomorph.coe_trans_symm,OpenPartialHomeomorph.symm_symm,
    Homeomorph.refl_apply,Function.comp_def,id_eq,d.right_inv inside.1] using derivative

theorem inverse_det_ne_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (e d : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (inside : y ∈ (e.symm.trans d).target) :
    (fderiv ℝ (e.symm.trans d).symm y).det ≠ 0 := by
  obtain ⟨L,derivative⟩ := inverse_hasFDerivAt e d he hd y inside
  rw [derivative.fderiv]
  exact L.toLinearEquiv.isUnit_det'.ne_zero

end LeanShared.ChartTransitionJacobian
