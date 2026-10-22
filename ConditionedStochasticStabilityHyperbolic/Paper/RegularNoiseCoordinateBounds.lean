module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformChartWords
public import LeanShared.Geometry.ChartMapC1Globalization

/-! Literal Whitney assumptions give uniform chart value and spatial
 derivative bounds for all positive scales and all their controls in one
 small window. No continuity of the family with respect to scale is used. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

theorem Maps.uniform_coordinate_bounds
    {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T:M≃ₜM} {r:ℝ} (F:Maps (E:=E) (ι:=ι) T r) (hr:1≤r)
    (hT:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (K:Set E) (compact:IsCompact K)
    (inside:K⊆LeanShared.ChartMapC1Globalization.domain c d T) :
    ∃η:NNReal,0<η ∧ ∃B D:ℝ,0≤B ∧ 0≤D ∧
      ∀ ε:NNReal,0<ε→ε≤η→∀ control:cube (ι:=ι) ε,∀ x∈K,
        ‖d (F.family ε control.val (c.symm x))‖≤B ∧
        ‖fderiv ℝ (fun y=>d (F.family ε control.val (c.symm y))) x‖≤D := by
  let g:E→E:=fun x=>d (T (c.symm x))
  have smooth:∀ x∈K,ContDiffAt ℝ 1 g x:=by
    intro x hx
    have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c.symm x:=
      (contMDiffAt_symm_of_mem_maximalAtlas hc (inside hx).1).of_le (by simp)
    have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d (T (c.symm x)):=
      (contMDiffAt_of_mem_maximalAtlas hd (inside hx).2).of_le (by simp)
    exact (last.comp x (hT.contMDiffAt.comp x first)).contDiffAt
  have cg:ContinuousOn g K:=fun x hx=>(smooth x hx).continuousAt.continuousWithinAt
  have cd:ContinuousOn (fderiv ℝ g) K:=fun x hx=>
    ((smooth x hx).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨B,hB,boundB⟩:=(compact.image_of_continuousOn cg).isBounded.exists_pos_norm_le
  obtain ⟨D,hD,boundD⟩:=(compact.image_of_continuousOn cd).isBounded.exists_pos_norm_le
  have valid:K⊆c.target∩((T:M→M)^[1]∘c.symm)⁻¹'d.source:=by
    simpa only [Function.iterate_one,Function.comp_def,LeanShared.ChartMapC1Globalization.domain] using inside
  obtain ⟨η,hη,est⟩:=F.uniform_chart_word_jets hr hT c d hc hd 1 K compact valid 1 zero_lt_one
  refine ⟨η,hη,B+1,D+1,by linarith,by linarith,?_⟩
  intro ε hp hw control x hx
  have step:=est ε hp hw (fun _=>control) x hx
  have estimate:‖d (F.family ε control.val (c.symm x))-g x‖+
      ‖fderiv ℝ (fun y=>d (F.family ε control.val (c.symm y))) x-fderiv ℝ g x‖≤1:=by
    simpa only [LeanShared.FiniteJetComposition.word,Function.comp_def,
      Function.id_def,Function.iterate_one] using step
  have b:=boundB (g x) ⟨x,hx,rfl⟩
  have dd:=boundD (fderiv ℝ g x) ⟨x,hx,rfl⟩
  constructor
  · have triangle:=norm_le_norm_sub_add (d (F.family ε control.val (c.symm x))) (g x)
    have nonneg:=norm_nonneg (fderiv ℝ (fun y=>d (F.family ε control.val (c.symm y))) x-fderiv ℝ g x)
    linarith
  · have triangle:=norm_le_norm_sub_add (fderiv ℝ (fun y=>d (F.family ε control.val (c.symm y))) x) (fderiv ℝ g x)
    have nonneg:=norm_nonneg (d (F.family ε control.val (c.symm x))-g x)
    linarith
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
