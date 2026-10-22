module
public import LeanShared.Geometry.FiniteSmoothReferenceJacobianLocal
public import LeanShared.MeasureTheory.CoordinateJacobianCocycle
import all LeanShared.Geometry.FiniteSmoothReferenceLocalDensity

/-! Exact local chart formulas for the computed reference Jacobian. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold
open scoped Topology Manifold ContDiff

private theorem transported_density
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (H : M ≃ₜ M) (e c : OpenPartialHomeomorph M E) (p : E → ℝ) (y : E) :
    CoordinateJacobianDensity.density (H.symm.transOpenPartialHomeomorph e)
      (H.symm.transOpenPartialHomeomorph c) p y =
      CoordinateJacobianDensity.density e c p y := by
  classical
  have same : (fun z => ((H.symm.transOpenPartialHomeomorph e).symm.trans
      (H.symm.transOpenPartialHomeomorph c)).symm z) =
      fun z => (e.symm.trans c).symm z := by
    funext z
    change e (H.symm (H (c.symm z))) = e (c.symm z)
    rw [H.symm_apply_apply]
  have target : ((H.symm.transOpenPartialHomeomorph e).symm.trans
      (H.symm.transOpenPartialHomeomorph c)).target = (e.symm.trans c).target := by
    ext z
    change (z ∈ c.target ∧ H (c.symm z) ∈ H.symm ⁻¹' e.source) ↔
      (z ∈ c.target ∧ c.symm z ∈ e.source)
    simp only [mem_preimage,H.symm_apply_apply]
  unfold CoordinateJacobianDensity.density
  rw [target]
  change (if y ∈ (e.symm.trans c).target then
    |(fderiv ℝ (fun z => ((H.symm.transOpenPartialHomeomorph e).symm.trans
      (H.symm.transOpenPartialHomeomorph c)).symm z) y).det| *
      p (((H.symm.transOpenPartialHomeomorph e).symm.trans
      (H.symm.transOpenPartialHomeomorph c)).symm y) else 0) = _
  rw [same]
  congr 2
  exact congrArg p (congrFun same y)


set_option maxHeartbeats 1600000 in
theorem Data.pushforwardDensity_factor
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (s : Data (E := E) (M := M)) (H : M ≃ₜ M)
    (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (hy : y ∈ d.target) (inside : H.symm (d.symm y) ∈ c.source) :
    s.pushforwardDensity H d y =
      |(fderiv ℝ (c ∘ H.symm ∘ d.symm) y).det| *
        s.localDensity c (c (H.symm (d.symm y))) := by
  classical
  have cDiff : c.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hc).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hc).mdifferentiableOn (by simp)⟩
  have dDiff : d.MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas hd).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas hd).mdifferentiableOn (by simp)⟩
  obtain ⟨L,derivative⟩ := DiffeomorphismChartDerivative.exists_equivalence H.symm
    (inverse.mdifferentiable (by simp)) (forward.mdifferentiable (by simp)) d c dDiff cDiff
    (d.symm y) (d.map_target hy) inside
  have first : DifferentiableAt ℝ (c ∘ H.symm ∘ d.symm) y := by
    have actual := derivative.differentiableAt
    rwa [d.right_inv hy] at actual
  unfold Data.pushforwardDensity FiniteChartDensity.density Data.localDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let C := H.symm.transOpenPartialHomeomorph c
  have last (member : d.symm y ∈ (s.transportedChart H i).source) :
      DifferentiableAt ℝ ((s.transportedChart H i) ∘ C.symm) (C (d.symm y)) := by
    have point : C (d.symm y) ∈ ((chartAt E i).symm.trans c).target :=
      by
        refine ⟨c.map_source inside,?_⟩
        change c.symm (c (H.symm (d.symm y))) ∈ (chartAt E i).source
        rw [c.left_inv inside]
        exact member
    have actual := ((transition_regular (chartAt E i) c (chart_mem_maximalAtlas i) hc
      _ point).contDiffAt (((chartAt E i).symm.trans c).open_target.mem_nhds point)).differentiableAt (by simp)
    have same : ((s.transportedChart H i) ∘ C.symm) = ((chartAt E i).symm.trans c).symm := by
      funext z
      change (chartAt E i) (H.symm (H (c.symm z))) = (chartAt E i) (c.symm z)
      rw [H.symm_apply_apply]
    rw [same]
    exact actual
  have factor := CoordinateJacobianDensity.factor (s.transportedChart H i) C d (s.density i) y
    hy inside first last
  change CoordinateJacobianDensity.density (s.transportedChart H i) d (s.density i) y =
    |(fderiv ℝ (c ∘ H.symm ∘ d.symm) y).det| *
      CoordinateJacobianDensity.density (H.symm.transOpenPartialHomeomorph (chartAt E i))
        (H.symm.transOpenPartialHomeomorph c) (s.density i) (c (H.symm (d.symm y))) at factor
  rw [transported_density] at factor
  exact factor


theorem Data.jacobian_eq_inverse_chart_density
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (s : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (H : M ≃ₜ M) (forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 H.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (x : M) (hx : x ∈ d.source) (inside : H.symm x ∈ c.source) :
    s.jacobian H x =
      |(fderiv ℝ (c ∘ H.symm ∘ d.symm) (d x)).det| *
        s.localDensity c (c (H.symm x)) / s.localDensity d (d x) := by
  rw [s.jacobian_eq_chart_ratio μ H forward inverse d hd hx]
  have factor := s.pushforwardDensity_factor H forward inverse c d hc hd (d x)
    (d.map_source hx) (by rwa [d.left_inv hx])
  rw [d.left_inv hx] at factor
  dsimp only
  rw [factor]

end LeanShared.FiniteSmoothReferenceCharts
