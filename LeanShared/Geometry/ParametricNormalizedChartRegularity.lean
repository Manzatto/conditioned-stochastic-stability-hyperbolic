module
public import LeanShared.Geometry.ContinuousCenteredFrameCharts
public import LeanShared.Analysis.CenteredFrameDerivative
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Joint C1 regularity in the actual genuine charts and fixed linear
normalizations. The parameter and normalized model have independent types. -/
public noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.ParametricNormalizedChartRegularity
variable {A E P M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace E M]

theorem contDiffAt_centered (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (L R : P ≃L[ℝ] E) (a b : E) (f : A × M → M)
    (O : Set A) (openO : IsOpen O)
    (joint : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 f (O ×ˢ univ))
    (q : A × P) (parameter : q.1 ∈ O) (source : a+L q.2 ∈ c.target)
    (target : f (q.1,c.symm (a+L q.2)) ∈ d.source) :
    ContDiffAt ℝ 1 (fun z : A × P =>
      CenteredManifoldCoordinates.centered L R a b (d ∘ (fun x => f (z.1,x)) ∘ c.symm) z.2) q := by
  have affine : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,P))) (𝓘(ℝ,E)) 1
      (fun z : A × P => a+L z.2) q :=
    contMDiffAt_const.add (L.contDiff.contMDiff.contMDiffAt.comp q contMDiffAt_snd)
  have inverseChart : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 c.symm (a+L q.2) :=
    (contMDiffAt_symm_of_mem_maximalAtlas hc source).of_le (by simp)
  have decode : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,P))) (𝓘(ℝ,E)) 1
      (fun z : A × P => c.symm (a+L z.2)) q := by
    exact inverseChart.comp q affine
  have first : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,P))) ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) 1
      (fun z : A × P => (z.1,c.symm (a+L z.2))) q := contMDiffAt_fst.prodMk decode
  have family := ((joint (q.1,c.symm (a+L q.2)) ⟨parameter,mem_univ _⟩).contMDiffAt
    ((openO.prod isOpen_univ).mem_nhds ⟨parameter,mem_univ _⟩)).comp q first
  have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d (f (q.1,c.symm (a+L q.2))) :=
    (contMDiffAt_of_mem_maximalAtlas hd target).of_le (by simp)
  have raw := last.comp q family
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at raw
  have coordinate : ContDiffAt ℝ 1 (fun z : A × P => d (f (z.1,c.symm (a+L z.2)))) q :=
    raw.contDiffAt
  exact R.symm.contDiff.contDiffAt.comp q (coordinate.sub contDiffAt_const)

end LeanShared.ParametricNormalizedChartRegularity
