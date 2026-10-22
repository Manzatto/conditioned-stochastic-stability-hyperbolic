module
public import LeanShared.Geometry.FiniteSmoothReferenceJacobianFormula

/-! Uniform actual reference-Jacobian value bounds from bounded inverse
coordinate derivatives and compact chart captures. -/
public noncomputable section
namespace LeanShared.FiniteSmoothReferenceCharts
open Set MeasureTheory Measure IsManifold Metric
open scoped Topology Manifold ContDiff

theorem Data.jacobian_local_bound
    {E M P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace M] [T2Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (s : Data (E := E) (M := M)) (μ : Measure E) [IsAddHaarMeasure μ]
    (family : P → M ≃ₜ M)
    (forward : ∀ p, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (family p))
    (inverse : ∀ p, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (family p).symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (K L : Set E) (compactK : IsCompact K) (sourceK : K ⊆ d.target)
    (compactL : IsCompact L) (sourceL : L ⊆ c.target)
    (M0 : ℝ)
    (capture : ∀ p x, x ∈ K → (family p).symm (d.symm x) ∈ c.source)
    (image : ∀ p x, x ∈ K → c ((family p).symm (d.symm x)) ∈ L)
    (bounded : ∀ p x, x ∈ K → ‖fderiv ℝ (c ∘ (family p).symm ∘ d.symm) x‖ ≤ M0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p x, x ∈ K → |s.jacobian (family p) (d.symm x)| ≤ B := by
  obtain ⟨Ap,boundP⟩ := compactL.exists_bound_of_continuousOn
    ((s.localDensity_continuousOn c hc).mono sourceL)
  obtain ⟨Aq,boundQ⟩ := compactK.exists_bound_of_continuousOn
    ((((s.localDensity_continuousOn d hd).inv₀
      (fun z hz => (s.localDensity_positive d hd z hz).ne')).mono sourceK))
  obtain ⟨Ad,boundD⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) M0).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  let Bp := max 0 Ap
  let Bq := max 0 Aq
  let Bd := max 0 Ad
  refine ⟨Bd*Bp*Bq,mul_nonneg (mul_nonneg (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _),?_⟩
  intro p x hx
  rw [s.jacobian_eq_inverse_chart_density μ (family p) (forward p) (inverse p) c d hc hd
    (d.symm x) (d.map_target (sourceK hx)) (capture p x hx), d.right_inv (sourceK hx)]
  rw [div_eq_mul_inv,abs_mul,abs_mul,abs_abs]
  have db : |(fderiv ℝ (c ∘ (family p).symm ∘ d.symm) x).det| ≤ Bd := by
    simpa only [Real.norm_eq_abs] using
      (boundD _ (by simpa only [mem_closedBall,dist_zero_right] using bounded p x hx)).trans (le_max_right _ _)
  have pb : |s.localDensity c (c ((family p).symm (d.symm x)))| ≤ Bp := by
    simpa only [Real.norm_eq_abs] using (boundP _ (image p x hx)).trans (le_max_right _ _)
  have qb : |(s.localDensity d x)⁻¹| ≤ Bq := by
    simpa only [Real.norm_eq_abs,Pi.inv_apply,Bq] using (boundQ _ hx).trans (le_max_right _ _)
  exact mul_le_mul (mul_le_mul db pb (abs_nonneg _) (le_max_left _ _)) qb
    (abs_nonneg _) (mul_nonneg (le_max_left _ _) (le_max_left _ _))

end LeanShared.FiniteSmoothReferenceCharts
