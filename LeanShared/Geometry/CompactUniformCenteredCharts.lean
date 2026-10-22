module
public import LeanShared.Geometry.CompactCenteredAtlasRadius
public import LeanShared.Geometry.CompactChartPairCover

/-! A finite family of actual centered atlas charts with one common nonlinear
radius. This is constructed from compact Riemannian geometry and the actual
C¹ map; neither chart-domain validity nor derivative remainder estimates are
input certificates. -/
public noncomputable section
namespace LeanShared.CompactUniformCenteredCharts
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
open LeanShared.CenteredManifoldCoordinates

private theorem common_positive {I : Type*} (s : Finset I) (r : I → ℝ)
    (positive : ∀ i ∈ s, 0 < r i) : ∃ R > 0, ∀ i ∈ s, R ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s outside ih =>
    obtain ⟨R, hR, bound⟩ := ih (fun j hj => positive j (Finset.mem_insert_of_mem hj))
    refine ⟨min R (r i), lt_min hR (positive i (Finset.mem_insert_self _ _)), fun j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (bound j hj)

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
  target : ∀ i, MapsTo H (patch i) (chartAt E (H i.val)).source
  cover : K ⊆ ⋃ i ∈ centers, interior (patch i)
  radius : ℝ
  positive : 0 < radius
  estimates : ∀ i ∈ centers, ∀ (x : M) (hx : x ∈ patch i)
    (e : P ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (f : Q ≃L[ℝ] TangentSpace (𝓘(ℝ, E)) (H x)),
    ‖e.toContinuousLinearMap‖ ≤ B → ‖f.symm.toContinuousLinearMap‖ ≤ B →
    let c := chartAt E i.val
    let d := chartAt E (H i.val)
    let C := CompactRiemannianChartBounds.chart_differentiable c (chart_mem_maximalAtlas i.val)
    let D := CompactRiemannianChartBounds.chart_differentiable d (chart_mem_maximalAtlas (H i.val))
    let L := (e.trans (C.mfderiv (source i hx))).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c x))
    let R := (f.trans (D.mfderiv (target i hx))).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (d (H x)))
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
  obtain ⟨centers, patch, facts, cover⟩ := CompactChartPairCover.exists_cover (E := E) (F := E) H smooth.continuous K compact
  have witnesses (i : K) := CompactCenteredAtlasRadius.exists_radius (P := P) (Q := Q)
    H smooth (chartAt E i.val) (chartAt E (H i.val))
    (chart_mem_maximalAtlas i.val) (chart_mem_maximalAtlas (H i.val))
    (patch i) (facts i).1 (facts i).2.1 (facts i).2.2.1 B δ positiveB positiveδ
  choose radii positive estimates using witnesses
  obtain ⟨radius, positiveRadius, common⟩ := common_positive centers radii (fun i _ => positive i)
  refine ⟨{
    centers := centers
    patch := patch
    compact := fun i => (facts i).1
    source := fun i => (facts i).2.1
    target := fun i => (facts i).2.2.1
    cover := cover
    radius := radius
    positive := positiveRadius
    estimates := ?_
  }⟩
  intro i hi x hx e f he hf
  dsimp only
  intro z hz
  exact estimates i x hx e f he hf z (hz.trans (common i hi))

end LeanShared.CompactUniformCenteredCharts
