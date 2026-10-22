module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseJets
public import LeanShared.Analysis.JetUniformOnCompact
import Mathlib.Tactic

/-! An actual common compact-domain inverse derivative bound, derived from
moving-point inverse jets and deterministic C1 regularity. There is no
assumed inverse Whitney rate or operator-norm bound. -/
public noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared.FiniteJetComposition

theorem InverseFamily.uniform_chart_derivative_bound
    {E M ι:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T:M≃ₜM} {r:ℝ} {F:Maps (E:=E) (ι:=ι) T r} (J:InverseFamily F) (hr:1≤r)
    (regular:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (c d:OpenPartialHomeomorph M E)
    (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd:d∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
    {K:Set E} (compact:IsCompact K) (valid:K⊆d.target∩(T.symm∘d.symm) ⁻¹' c.source) :
    ∃η:NNReal,0<η ∧ η≤J.window ∧∃B:ℝ,0≤B ∧
      ∀ε:NNReal,0<ε→ε≤η→∀a:cube (ι:=ι) ε,∀y∈K,
        ‖fderiv ℝ (c∘(fun x=>J.map ε (a.val,x))∘d.symm) y‖≤B :=by
  let U:=d.target∩(T.symm∘d.symm) ⁻¹' c.source
  let g:=c∘T.symm∘d.symm
  have smooth:∀y∈U,ContDiffAt ℝ 1 g y:=by
    intro y hy
    have first:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d.symm y:=
      (contMDiffAt_symm_of_mem_maximalAtlas hd hy.1).of_le (by simp)
    have last:ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c (T.symm (d.symm y)):=
      (contMDiffAt_of_mem_maximalAtlas hc hy.2).of_le (by simp)
    exact (last.comp y (inverse.contMDiffAt.comp y first)).contDiffAt
  have continuousD:ContinuousOn (fderiv ℝ g) K:=fun y hy=>
    ((smooth y (valid hy)).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨B,hB,boundB⟩:=(compact.image_of_continuousOn continuousD).isBounded.exists_pos_norm_le
  obtain ⟨η,hη,estimate⟩:=uniform_on_compact (fun ε=>cube (ι:=ι) ε)
    (fun ε a=>c∘(fun y=>J.map ε (a.val,y))∘d.symm) g U K compact valid smooth
    (fun ε controls limit pos=>J.actual_jets_in_charts hr regular inverse ε controls _ limit
      (Filter.Eventually.of_forall pos) c d hc hd) 1 zero_lt_one
  refine ⟨min η J.window,lt_min hη J.positive,min_le_right _ _,B+1,by positivity,?_⟩
  intro ε hp hw a y hy
  have comparison:‖fderiv ℝ (c∘(fun x=>J.map ε (a.val,x))∘d.symm) y-fderiv ℝ g y‖≤1:=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (estimate ε hp (hw.trans (min_le_left _ _)) a y hy)
  exact (norm_le_norm_sub_add _ _).trans
    ((add_le_add comparison (boundB _ ⟨y,hy,rfl⟩)).trans_eq (by ring))
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
