module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseJetConvergence
public import LeanShared.Analysis.LocalJetCoordinateChanges

/-! Join literal Whitney chart pairs along an actual deterministic itinerary.
The next source chart may differ from the current target chart. Smooth chart
transitions and actual inverse identities derive the corresponding noisy jet
convergence, without assuming a new Whitney estimate in the joined charts. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition

namespace WhitneyAtlas
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] {T : M → M} (A : WhitneyAtlas (E := E) T)

@[expose] def transition (i j : Fin A.count) : E → E := A.source j ∘ (A.target i).symm
@[expose] def transitionDomain (i j : Fin A.count) : Set E :=
  (A.target i).target ∩ (A.target i).symm ⁻¹' (A.source j).source
@[expose] def stepDomain (i j : Fin A.count) : Set E :=
  A.coordinatePatch i ∩ (T ∘ (A.source i).symm) ⁻¹' (A.source j).source
@[expose] def stepCoordinate (f : M → M) (i j : Fin A.count) : E → E :=
  A.source j ∘ f ∘ (A.source i).symm

omit [FiniteDimensional ℝ E] in
theorem transition_smooth [IsManifold (𝓘(ℝ, E)) ∞ M]
    (i j : Fin A.count) (y : E) (hy : y ∈ A.transitionDomain i j) :
    ContDiffAt ℝ 1 (A.transition i j) y := by
  have first : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (A.target i).symm y :=
    (contMDiffAt_symm_of_mem_maximalAtlas (A.target_smooth i) hy.1).of_le (by simp)
  have second : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (A.source j) ((A.target i).symm y) :=
    (contMDiffAt_of_mem_maximalAtlas (A.source_smooth j) hy.2).of_le (by simp)
  exact (second.comp y first).contDiffAt

omit [FiniteDimensional ℝ E] in
theorem stepDomain_open (continuous : Continuous T) (i j : Fin A.count) :
    IsOpen (A.stepDomain i j) := by
  have openPatch : IsOpen (A.coordinatePatch i) :=
    (A.source i).isOpen_inter_preimage_symm (A.patch_open i)
  have continuousOn : ContinuousOn (T ∘ (A.source i).symm) (A.coordinatePatch i) :=
    (continuous.comp_continuousOn (A.source i).symm.continuousOn).mono (fun _ h => h.1)
  exact continuousOn.isOpen_inter_preimage openPatch (A.source j).open_source

omit [FiniteDimensional ℝ E] in
theorem coordinate_maps_transition (i j : Fin A.count) :
    MapsTo (A.coordinate T i) (A.stepDomain i j) (A.transitionDomain i j) := by
  intro y hy
  have inside : T ((A.source i).symm y) ∈ (A.target i).source :=
    A.deterministic_target i (mem_image_of_mem T (subset_closure hy.1.2))
  refine ⟨(A.target i).map_source inside, ?_⟩
  change (A.target i).symm ((A.target i) (T ((A.source i).symm y))) ∈ (A.source j).source
  rw [(A.target i).left_inv inside]
  exact hy.2

omit [FiniteDimensional ℝ E] in
theorem transition_coordinate_eq (f : M → M)
    (target : ∀ k, f '' closure (A.patch k) ⊆ (A.target k).source)
    (i j : Fin A.count) :
    EqOn (A.transition i j ∘ A.coordinate f i) (A.stepCoordinate f i j)
      (A.stepDomain i j) := by
  intro y hy
  have inside := target i (mem_image_of_mem f (subset_closure hy.1.2))
  change (A.source j) ((A.target i).symm ((A.target i) (f ((A.source i).symm y)))) = _
  rw [(A.target i).left_inv inside]
  rfl

end WhitneyAtlas

theorem Maps.itinerary_jetConvergesOn
    {E M ι A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (i j : Fin F.atlas.count) :
    JetConvergesOn (fun a => F.atlas.stepCoordinate (F.family (ε a) (controls a).val) i j)
      (F.atlas.stepCoordinate T i j) l (F.atlas.stepDomain i j) := by
  have noisy := (F.coordinate_jetConvergesOn regularity deterministic ε controls l
    limit positive i).mono (V := F.atlas.stepDomain i j) (fun _ h => h.1)
  have transition := JetConvergesOn.constant (F.atlas.transition i j) l
    (F.atlas.transitionDomain i j) (F.atlas.transition_smooth i j)
  have combined := transition.comp noisy (F.atlas.coordinate_maps_transition i j)
  apply combined.congr_on_open (F.atlas.stepDomain_open T.continuous i j)
  · have window : ∀ᶠ a in l, ε a ≤ F.window :=
      (limit.eventually (gt_mem_nhds F.window_positive)).mono (fun _ h => h.le)
    filter_upwards [positive, window] with a ha hw
    exact F.atlas.transition_coordinate_eq _
      (F.whitney_bound (ε a) ha hw (controls a)).target_control i j
  · exact F.atlas.transition_coordinate_eq _ F.atlas.deterministic_target i j

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
