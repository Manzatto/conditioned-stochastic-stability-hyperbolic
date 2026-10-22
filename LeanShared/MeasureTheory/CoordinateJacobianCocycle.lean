module
public import LeanShared.MeasureTheory.CoordinateJacobianDensity
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! The actual determinant-density cocycle through an intermediate chart.
Only ordinary derivatives at the point are used; no density compatibility
or completed-space identity is assumed. -/
public noncomputable section
namespace LeanShared.CoordinateJacobianDensity
open Set Filter
open scoped Topology

set_option maxHeartbeats 1600000 in
theorem factor
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M]
    (e c d : OpenPartialHomeomorph M E) (p : E → ℝ) (y : E)
    (hy : y ∈ d.target) (hc : d.symm y ∈ c.source)
    (first : DifferentiableAt ℝ (c ∘ d.symm) y)
    (last : d.symm y ∈ e.source → DifferentiableAt ℝ (e ∘ c.symm) (c (d.symm y))) :
    density e d p y = |(fderiv ℝ (c ∘ d.symm) y).det| *
      density e c p (c (d.symm y)) := by
  classical
  have middle : c (d.symm y) ∈ c.target := c.map_source hc
  have inverse : c.symm (c (d.symm y)) = d.symm y := c.left_inv hc
  by_cases he : d.symm y ∈ e.source
  · have ed : y ∈ (e.symm.trans d).target := ⟨hy,he⟩
    have ec : c (d.symm y) ∈ (e.symm.trans c).target := ⟨middle,by change c.symm (c (d.symm y)) ∈ e.source; rwa [inverse]⟩
    have same : (e ∘ d.symm) =ᶠ[𝓝 y] ((e ∘ c.symm) ∘ (c ∘ d.symm)) := by
      have near : ∀ᶠ z in 𝓝 y, z ∈ d.target ∧ d.symm z ∈ c.source :=
        Filter.Eventually.and (d.open_target.mem_nhds hy)
          ((d.continuousAt_symm hy).preimage_mem_nhds (c.open_source.mem_nhds hc))
      filter_upwards [near] with z hz
      simp only [Function.comp_apply,c.left_inv hz.2]
    have derivative := ((last he).hasFDerivAt.comp y first.hasFDerivAt).congr_of_eventuallyEq same
    have chain : fderiv ℝ (e ∘ d.symm) y =
        (fderiv ℝ (e ∘ c.symm) (c (d.symm y))).comp (fderiv ℝ (c ∘ d.symm) y) :=
      derivative.fderiv
    change (if y ∈ (e.symm.trans d).target then _ else _) =
      _ * (if c (d.symm y) ∈ (e.symm.trans c).target then _ else _)
    rw [ite_eq_left ed,ite_eq_left ec]
    simp only [OpenPartialHomeomorph.coe_trans_symm,OpenPartialHomeomorph.symm_symm,
      Function.comp_apply,inverse]
    rw [chain]
    change |LinearMap.det ((fderiv ℝ (e ∘ c.symm) (c (d.symm y))).toLinearMap.comp
      (fderiv ℝ (c ∘ d.symm) y).toLinearMap)| * _ = _
    rw [LinearMap.det_comp,abs_mul]
    ring
  · have ed : y ∉ (e.symm.trans d).target := fun h => he h.2
    have ec : c (d.symm y) ∉ (e.symm.trans c).target := fun h => he (by have q : c.symm (c (d.symm y)) ∈ e.source := h.2; rwa [inverse] at q)
    change (if y ∈ (e.symm.trans d).target then _ else _) =
      _ * (if c (d.symm y) ∈ (e.symm.trans c).target then _ else _)
    rw [ite_eq_right ed,ite_eq_right ec,mul_zero]

end LeanShared.CoordinateJacobianDensity
