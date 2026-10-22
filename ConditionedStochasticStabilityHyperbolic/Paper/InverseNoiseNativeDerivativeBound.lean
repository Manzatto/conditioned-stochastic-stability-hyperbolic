module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseDerivativeBound
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseUniformCapture
public import LeanShared.Geometry.RiemannianDerivativeChartFactor
public import LeanShared.Analysis.CompactUniformWindowBound
import Mathlib.Tactic

/-! Uniform native Riemannian inverse-derivative bounds for the ORIGINAL
noise maps, derived from actual compact coordinate jets and chart calculus.
No inverse Whitney rate or native operator bound is assumed. -/
public noncomputable section
set_option maxHeartbeats 3200000
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle Metric Filter
open scoped Topology Manifold ContDiff Bundle NNReal

theorem InverseFamily.uniform_native_derivative_bound
    {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (hr : 1 ≤ r)
    (regular : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧ ∃ B : ℝ, 0 < B ∧
      ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ control : cube (ι := ι) ε, ∀ x : M,
        ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun z => J.map ε (control.val,z)) x‖ ≤ B := by
  classical
  let P := Σ ε : {ε : ℝ≥0 // 0 < ε ∧ ε ≤ J.window}, cube (ι := ι) ε.val
  let f : P → M → ℝ := fun p x => ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E))
    (fun z => J.map p.1.val (p.2.val,z)) x‖
  have localBound : ∀ x : M, ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      ∃ η : ℝ≥0, 0 < η ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ p : P, p.1.val ≤ η → ∀ z ∈ W, ‖f p z‖ ≤ B := by
    intro x
    let d := chartAt E x
    let c := chartAt E (T.symm x)
    have hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M := chart_mem_maximalAtlas x
    have hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M := chart_mem_maximalAtlas (T.symm x)
    have dx : x ∈ d.source := mem_chart_source E x
    have cx : T.symm x ∈ c.source := mem_chart_source E (T.symm x)
    let y := d x
    let center := c (T.symm x)
    obtain ⟨R,hR,sourceR⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source cx))
    let ρ := R/2
    have hρ : 0 < ρ := half_pos hR
    let L := closedBall center ρ
    have sourceL : L ⊆ c.target := (closedBall_subset_ball (half_lt_self hR)).trans sourceR
    let U := c.source ∩ c ⁻¹' ball center ρ
    have openU : IsOpen U := c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball
    have inU : T.symm (d.symm y) ∈ U := by
      rw [d.left_inv dx]
      exact ⟨cx,mem_ball_self hρ⟩
    have near : (T.symm ∘ d.symm) ⁻¹' U ∈ 𝓝 y :=
      (T.symm.continuous.continuousAt.comp (d.continuousAt_symm (d.map_source dx))).preimage_mem_nhds (openU.mem_nhds inU)
    obtain ⟨R0,hR0,source0⟩ := Metric.mem_nhds_iff.mp (inter_mem (d.open_target.mem_nhds (d.map_source dx)) near)
    let δ := R0/2
    have hδ : 0 < δ := half_pos hR0
    let K := closedBall y δ
    have subK : K ⊆ d.target ∩ (T.symm ∘ d.symm) ⁻¹' U :=
      (closedBall_subset_ball (half_lt_self hR0)).trans source0
    have sourceK : K ⊆ d.target := fun q hq => (subK hq).1
    have domainCompact : IsCompact (d.symm '' K) := (isCompact_closedBall y δ).image_of_continuousOn
      (d.continuousOn_symm.mono sourceK)
    have targetCompact : IsCompact (c.symm '' L) := (isCompact_closedBall center ρ).image_of_continuousOn
      (c.continuousOn_symm.mono sourceL)
    have domainSource : d.symm '' K ⊆ d.source := by rintro _ ⟨q,hq,rfl⟩; exact d.map_target (sourceK hq)
    have targetSource : c.symm '' L ⊆ c.source := by rintro _ ⟨q,hq,rfl⟩; exact c.map_target (sourceL hq)
    obtain ⟨ηj,hηj,wj,Bj,hBj,jets⟩ := J.uniform_chart_derivative_bound hr regular inverse c d hc hd
      (isCompact_closedBall y δ) (fun q hq => ⟨(subK hq).1,(subK hq).2.1⟩)
    obtain ⟨ηc,hηc,wc,capture⟩ := J.exists_uniform_target (d.symm '' K) U domainCompact openU
      (by rintro _ ⟨q,hq,rfl⟩; exact (subK hq).2)
    obtain ⟨Cd,hCd,boundD⟩ := LeanShared.CompactRiemannianChartBounds.forward d hd (d.symm '' K) domainCompact domainSource
    obtain ⟨Cc,hCc,boundC⟩ := LeanShared.CompactRiemannianChartBounds.inverse c hc (c.symm '' L) targetCompact targetSource
    let W := d.source ∩ d ⁻¹' ball y δ
    have openW : IsOpen W := d.continuousOn.isOpen_inter_preimage d.open_source isOpen_ball
    have inW : x ∈ W := ⟨dx,mem_ball_self hδ⟩
    refine ⟨W,openW,inW,min ηj ηc,lt_min hηj hηc,Cc*Bj*Cd,by positivity,?_⟩
    intro p hp z hz
    have point : d z ∈ K := ball_subset_closedBall hz.2
    have member : z ∈ d.symm '' K := ⟨d z,point,d.left_inv hz.1⟩
    have captured : J.map p.1.val (p.2.val,z) ∈ U := capture p.1.val p.1.property.1
      (hp.trans (min_le_right _ _)) p.2 member
    have targetMember : J.map p.1.val (p.2.val,z) ∈ c.symm '' L :=
      ⟨c (J.map p.1.val (p.2.val,z)),ball_subset_closedBall captured.2,c.left_inv captured.1⟩
    have bound := LeanShared.RiemannianDerivativeChartFactor.norm_le
      (fun q => J.map p.1.val (p.2.val,q))
      ((J.map_contMDiff p.1.val p.1.property.1 p.1.property.2 p.2).mdifferentiable (by simp)) d c
      (LeanShared.CompactRiemannianChartBounds.chart_differentiable d hd)
      (LeanShared.CompactRiemannianChartBounds.chart_differentiable c hc) z hz.1 captured.1
    have inverseBound := boundC _ targetMember
    have forwardBound := boundD _ member
    have derivativeBound := jets p.1.val p.1.property.1 (hp.trans (min_le_left _ _)) p.2 (d z) point
    have estimate := bound.trans (mul_le_mul
      (mul_le_mul inverseBound derivativeBound (norm_nonneg _) hCc.le) forwardBound
      (by positivity) (mul_nonneg hCc.le hBj))
    have nonnegative : 0 ≤ f p z := by
      change 0 ≤ ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun q => J.map p.1.val (p.2.val,q)) z‖
      positivity
    rw [Real.norm_eq_abs,abs_of_nonneg nonnegative]
    exact estimate
  obtain ⟨η,hη,B,hB,bound⟩ := LeanShared.CompactUniformLocalHolder.window_bound f
    (fun p : P => p.1.val) localBound
  refine ⟨min η J.window,lt_min hη J.positive,min_le_right _ _,B+1,by linarith,?_⟩
  intro ε hp hw control x
  have actual := bound (⟨⟨ε,hp,hw.trans (min_le_right _ _)⟩,control⟩ : P)
    (hw.trans (min_le_left _ _)) x
  have improved := actual.trans (le_add_of_nonneg_right (a := B) zero_le_one)
  change |‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun z => J.map ε (control.val,z)) x‖| ≤ B+1 at improved
  exact (le_abs_self _).trans improved

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
