module
public import LeanShared.Dynamics.HyperbolicChartJetJacobian
public import LeanShared.Geometry.NativeFirstJetJacobianExt

/-! The finite-jet functional is the literal native determinant of an
actual manifold map. Consequently ordinary coordinate first-jet limits
give native Jacobian limits without noise-scale differentiability. -/
@[expose] public noncomputable section
open Set Filter Bundle IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
open ChartAffineJetFamily
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}

omit [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)] in
theorem chartJetJacobian_actual (a : h.NormedAdaptedProjection)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (f : M → M) (x : M) (source : x ∈ c.source) (target : f x ∈ d.source)
    (regular : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x) :
    a.chartJetJacobian c d (c x,d (f x),fderiv ℝ (d ∘ f ∘ c.symm) (c x)) =
      ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)).normDet := by
  let q : Jet E := (c x,d (f x),fderiv ℝ (d ∘ f ∘ c.symm) (c x))
  let g : M → M := fun m => synthesis c d (q,m)
  have value : g x = f x := synthesis_at_center c d f x q.2.2 target
  have point : (q,x) ∈ domain c d := by
    refine ⟨source,?_⟩
    change d (f x) + q.2.2 (c x-c x) ∈ d.target
    rw [sub_self,map_zero,add_zero]
    exact d.map_source target
  have atPoint := ((synthesis_regular c d hc hd) (q,x) point).contMDiffAt
    ((domain_open c d hc).mem_nhds point)
  have smoothG : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) g x :=
    (atPoint.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by simp)
  have jet : fderiv ℝ (d ∘ g ∘ c.symm) (c x) = fderiv ℝ (d ∘ f ∘ c.symm) (c x) :=
    coordinate_fderiv c d q (c.map_source source) (d.map_source target)
  have same := NativeFirstJetJacobianExt.normDet_eq g f x c d
    (CompactRiemannianChartBounds.chart_differentiable c hc)
    (CompactRiemannianChartBounds.chart_differentiable d hd)
    source (value.symm ▸ target) target smoothG regular value jet (a.unstable x)
  have decode := congrArg (fun y : M =>
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) g y).toLinearMap.domRestrict (a.unstable y)).normDet)
    (c.left_inv source)
  exact decode.trans same

theorem tendsto_nativeJacobian_of_coordinateJets (a : h.NormedAdaptedProjection)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    {B : Type*} {l : Filter B} (f : B → M → M) (x : B → M) (f₀ : M → M) (x₀ : M)
    (source : x₀ ∈ c.source) (target : f₀ x₀ ∈ d.source) (collar : x₀ ∈ a.collar)
    (regular : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) f₀ x₀)
    (eventuallyValid : ∀ᶠ b in l, x b ∈ c.source ∧ f b (x b) ∈ d.source ∧
      MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) (f b) (x b))
    (jets : Tendsto (fun b => (c (x b),d (f b (x b)),fderiv ℝ (d ∘ f b ∘ c.symm) (c (x b)))) l
      (𝓝 (c x₀,d (f₀ x₀),fderiv ℝ (d ∘ f₀ ∘ c.symm) (c x₀)))) :
    Tendsto (fun b => ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (f b) (x b)).toLinearMap.domRestrict
      (a.unstable (x b))).normDet) l
      (𝓝 ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f₀ x₀).toLinearMap.domRestrict (a.unstable x₀)).normDet) := by
  have valid : (c x₀,d (f₀ x₀),fderiv ℝ (d ∘ f₀ ∘ c.symm) (c x₀)) ∈ a.validChartJets c d :=
    ⟨c.map_source source,d.map_source target,by simpa only [c.left_inv source] using collar⟩
  have limit := a.tendsto_chartJetJacobian c d hc hd valid jets
  rw [a.chartJetJacobian_actual c d hc hd f₀ x₀ source target regular] at limit
  apply limit.congr'
  filter_upwards [eventuallyValid] with b hb
  exact a.chartJetJacobian_actual c d hc hd (f b) (x b) hb.1 hb.2.1 hb.2.2

end LeanShared.HyperbolicBasicSet.HyperbolicData.NormedAdaptedProjection
