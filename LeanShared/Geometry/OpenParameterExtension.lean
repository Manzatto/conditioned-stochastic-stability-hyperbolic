module
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Extension from an open parameter set preserves local manifold regularity.
No behavior outside the open set is required. -/
public noncomputable section
namespace LeanShared.OpenParameterExtension
open Set IsManifold Filter
open scoped Topology Manifold ContDiff

@[expose] def extend {A M N : Type*} [TopologicalSpace A]
    (O : TopologicalSpace.Opens A) (f : O × M → N) (default : N) : A × M → N := by
  classical
  exact fun p => if h : p.1 ∈ O then f (⟨p.1,h⟩,p.2) else default

set_option maxHeartbeats 800000 in
theorem contMDiffAt
    {A E G M N : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [TopologicalSpace N] [ChartedSpace G N]
    (O : TopologicalSpace.Opens A) (f : O × M → N) (default : N)
    (a : O) (x : M)
    (smooth : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,G)) 1 f (a,x)) :
    ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,G)) 1 (extend O f default) (a.val,x) := by
  classical
  let e := chartAt A a
  have eval : e a = a.val := by simp [e,TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  have inside : a.val ∈ e.target := eval ▸ e.map_source (mem_chart_source A a)
  have inverseSmooth : ContMDiffAt (𝓘(ℝ,A)) (𝓘(ℝ,A)) 1 e.symm a.val :=
    (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℝ,A)) (n := ∞)
      (chart_mem_maximalAtlas a) inside).of_le (by decide)
  have inverseAt : e.symm a.val = a := by rw [←eval]; exact e.left_inv (mem_chart_source A a)
  have smooth' : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,G)) 1 f (e.symm a.val,x) := by
    rwa [inverseAt]
  have composed := smooth'.comp (a.val,x)
    ((inverseSmooth.comp (a.val,x) contMDiffAt_fst).prodMk contMDiffAt_snd)
  apply composed.congr_of_eventuallyEq
  have near : ∀ᶠ p : A × M in 𝓝 (a.val,x), p.1 ∈ e.target :=
    continuous_fst.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds inside)
  filter_upwards [near] with p hp
  have coe : (e.symm p.1).val = p.1 := by
    have raw := e.right_inv hp
    simpa [e,TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq] using raw
  have member : p.1 ∈ O := coe ▸ (e.symm p.1).property
  simp only [extend,dite_eq_left member]
  congr 1
  exact Prod.ext (Subtype.ext coe.symm) rfl

end LeanShared.OpenParameterExtension
