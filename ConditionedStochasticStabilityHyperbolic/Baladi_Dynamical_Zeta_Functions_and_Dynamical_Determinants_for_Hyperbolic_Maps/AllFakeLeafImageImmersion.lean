module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafGraphRegularity
public import LeanShared.Geometry.ParametrizedImmersionChart
public import LeanShared.Analysis.FakeLeafProjectionChart
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all LeanShared.Analysis.FakeLeafGraph

/-! Actual C¹ images of graph fake leaves are embedded C¹ submanifolds.
The atlas and immersion are constructed from the original graph chart and
the genuine local diffeomorphism, rather than assumed for the image. -/
public noncomputable section
open Set
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem C1Embedded.image_local_diffeomorphism {U : Submodule ℝ E} {Γ : Set E}
    [Nonempty Γ] (embedded : C1Embedded U Γ) {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖)
    (F : OpenPartialHomeomorph E E) (inside : Γ ⊆ F.source)
    (forward : ContDiffOn ℝ 1 F F.source) (backward : ContDiffOn ℝ 1 F.symm F.target) :
    C1Embedded U (F '' Γ) := by
  let q := FakeLeafGraph.projection U Γ
  let h := F.homeomorphOfImageSubsetSource inside rfl
  let p : (F '' Γ) → U := q ∘ h.symm
  let graph : U → E := fun u => (u : E) +
    (FakeLeafGraph.heightExtension U Γ hL slope u : E)
  let R : E → U := U.orthogonalProjectionOnto ∘ F.symm
  have domainOpen := embedded.projection_open hL slope
  let chart := FakeLeafProjectionChart.chart U Γ hL slope domainOpen
  have qopen : Topology.IsOpenEmbedding q := chart.isOpenEmbedding rfl
  have popen : Topology.IsOpenEmbedding p := qopen.comp h.symm.isOpenEmbedding
  have sameRange : range p = FakeLeafGraph.parameterDomain U Γ := by
    change range (q ∘ h.symm) = range q
    rw [Set.range_comp, Set.range_eq_univ.mpr h.symm.surjective, Set.image_univ]
  have graphRegular : ContDiffOn ℝ 1 graph (FakeLeafGraph.parameterDomain U Γ) :=
    U.subtypeL.contDiff.contDiffOn.add
      (Uᗮ.subtypeL.contDiff.comp_contDiffOn (embedded.heightExtension_contDiffOn hL slope))
  have graphImage : MapsTo graph (FakeLeafGraph.parameterDomain U Γ) Γ := by
    intro u hu
    exact (FakeLeafGraph.graphExtension_image U Γ hL slope).subset ⟨u, hu, rfl⟩
  have graphProjection (x : Γ) : graph (q x) = x.val := by
    change (q x : E) + (FakeLeafGraph.heightExtension U Γ hL slope (q x) : E) = x.val
    rw [FakeLeafGraph.heightExtension_on_domain U Γ hL slope ⟨q x, x, rfl⟩]
    rw [← FakeLeafGraph.point_eq_graph U Γ hL slope ⟨q x, x, rfl⟩,
      FakeLeafGraph.point_of_projection]
  let : Nonempty (F '' Γ) := ⟨h (Classical.choice ‹Nonempty Γ›)⟩
  refine ParametrizedImmersionChart.exists_chart (F '' Γ) p popen (F ∘ graph) ?_ ?_ R ?_ ?_
  · rw [sameRange]
    exact forward.comp graphRegular (fun _ hu => inside (graphImage hu))
  · intro x
    change F (graph (q (h.symm x))) = x.val
    rw [graphProjection]
    exact congrArg Subtype.val (h.apply_symm_apply x)
  · intro x
    rfl
  · intro x hx
    have target : x ∈ F.target := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact F.map_source (inside hy)
    exact U.orthogonalProjectionOnto.contDiff.contDiffAt.comp x
      (backward.contDiffAt (F.open_target.mem_nhds target))
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
