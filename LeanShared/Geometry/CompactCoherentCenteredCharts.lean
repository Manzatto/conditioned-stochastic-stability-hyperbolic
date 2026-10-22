module
public import LeanShared.Geometry.CompactUniformCenteredCharts
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! One finite chart cover, used coherently as both source and target along
orbits. Uniform estimates are constructed on every compact chart-pair
intersection. Thus an incoming target chart is exactly the next outgoing
source chart after a single pointwise chart selection. -/
public noncomputable section
namespace LeanShared.CompactCoherentCenteredCharts
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open LeanShared.CenteredManifoldCoordinates

variable {E M P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [T2Space M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

structure Data (H : M → M) (K : Set M) (B δ : ℝ) where
  centers : Finset K
  patch : K → Set M
  compact : ∀ i, IsCompact (patch i)
  source : ∀ i, patch i ⊆ (chartAt E i.val).source
  cover : K ⊆ ⋃ i ∈ centers, interior (patch i)
  radius : ℝ
  positive : 0 < radius
  estimates : ∀ i ∈ centers, ∀ j ∈ centers, ∀ (x : M)
    (hx : x ∈ patch i) (hy : H x ∈ patch j)
    (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (H x)),
    ‖e.toContinuousLinearMap‖ ≤ B → ‖f.symm.toContinuousLinearMap‖ ≤ B →
    let c := chartAt E i.val
    let d := chartAt E j.val
    let C := CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas i.val)
    let D := CompactRiemannianChartBounds.chart_differentiable d (chart_mem_maximalAtlas j.val)
    let L := (e.trans (C.mfderiv (source i hx))).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x))
    let R := (f.trans (D.mfderiv (source j hy))).trans (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x)))
    ∀ z : P, ‖z‖ ≤ radius →
      c x + L z ∈ c.target ∧ H (c.symm (c x + L z)) ∈ d.source ∧
      DifferentiableAt ℝ (centered L R (c x) (d (H x)) (d ∘ H ∘ c.symm)) z ∧
      ‖fderiv ℝ (centered L R (c x) (d (H x)) (d ∘ H ∘ c.symm)) z -
        f.symm.toContinuousLinearMap.comp
          ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H x).comp e.toContinuousLinearMap)‖ < δ

set_option maxHeartbeats 1600000 in
theorem exists_data (H : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 H)
    (K : Set M) (compact : IsCompact K) (B δ : ℝ) (positiveB : 0 < B) (positiveδ : 0 < δ) :
    Nonempty (Data (E := E) (P := P) (Q := Q) H K B δ) := by
  classical
  obtain ⟨centers, patch, facts, cover⟩ := CompactChartPairCover.exists_cover
    (E := E) (F := E) (id : M → M) continuous_id K compact
  have witnesses (ij : K × K) := CompactCenteredAtlasRadius.exists_radius (P := P) (Q := Q)
    H smooth (chartAt E ij.1.val) (chartAt E ij.2.val)
    (chart_mem_maximalAtlas ij.1.val) (chart_mem_maximalAtlas ij.2.val)
    (patch ij.1 ∩ H ⁻¹' patch ij.2)
    ((facts ij.1).1.inter_right ((facts ij.2).1.isClosed.preimage smooth.continuous))
    (fun _ hx => (facts ij.1).2.1 hx.1) (fun _ hx => (facts ij.2).2.1 hx.2)
    B δ positiveB positiveδ
  choose radii positive estimates using witnesses
  obtain ⟨radius, positiveRadius, common⟩ := CompactUniformCenteredCharts.common_positive
    (centers.product centers) radii (fun ij _ => positive ij)
  refine ⟨{
    centers := centers
    patch := patch
    compact := fun i => (facts i).1
    source := fun i => (facts i).2.1
    cover := cover
    radius := radius
    positive := positiveRadius
    estimates := ?_
  }⟩
  intro i hi j hj x hx hy e f he hf
  dsimp only
  intro z hz
  exact estimates (i,j) x ⟨hx,hy⟩ e f he hf z
    (hz.trans (common (i,j) (Finset.mem_product.mpr ⟨hi,hj⟩)))

end LeanShared.CompactCoherentCenteredCharts
