module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseCalculus
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseCloseness

/-! A coherently chosen inverse of the ORIGINAL noise family. This is a
constructed output, not an additional noise source. It preserves every noise
scale and every legal control. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Filter
open scoped Topology Manifold ContDiff NNReal

structure InverseFamily
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) where
  window : ℝ≥0
  positive : 0 < window
  window_le : window ≤ F.window
  map : ℝ≥0 → Control (ι := ι) × M → M
  domain : ℝ≥0 → Set (Control (ι := ι))
  open_domain : ∀ ε, IsOpen (domain ε)
  contains : ∀ ε, 0 < ε → ε ≤ window →
    (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set _) ⊆ domain ε
  smooth : ∀ ε, 0 < ε → ε ≤ window →
    ContMDiffOn ((𝓘(ℝ,Control (ι := ι))).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 (map ε) (domain ε ×ˢ univ)
  right : ∀ ε, 0 < ε → ε ≤ window → ∀ a ∈ domain ε, ∀ y, F.family ε a (map ε (a,y)) = y
  left : ∀ ε, 0 < ε → ε ≤ window → ∀ a ∈ domain ε, ∀ x, map ε (a,F.family ε a x) = x

set_option maxHeartbeats 3200000 in
def Maps.inverseFamily
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (default : M) : InverseFamily F := by
  classical
  have witness := F.exists_inverse_calculus regularity deterministic inverse default
  let η := Classical.choose witness
  have facts := Classical.choose_spec witness
  have choices : ∀ ε : ℝ≥0, ∃ J : Control (ι := ι) × M → M, ∃ U : Set (Control (ι := ι)),
      IsOpen U ∧ (0 < ε → ε ≤ η →
        (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set _) ⊆ U ∧
        ContMDiffOn ((𝓘(ℝ,Control (ι := ι))).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 J (U ×ˢ univ) ∧
        (∀ a ∈ U, ∀ y, F.family ε a (J (a,y)) = y) ∧
        ∀ a ∈ U, ∀ x, J (a,F.family ε a x) = x) := by
    intro ε
    by_cases h : 0 < ε ∧ ε ≤ η
    · obtain ⟨J,U,openU,contains,smooth,right,left,_rank⟩ := facts.2.2 ε h.1 h.2
      exact ⟨J,U,openU,fun _ _ => ⟨contains,smooth,right,left⟩⟩
    · exact ⟨fun p => T.symm p.2,univ,isOpen_univ,fun hp hw => False.elim (h ⟨hp,hw⟩)⟩
  choose J U openU properties using choices
  exact {
    window := η
    positive := facts.1
    window_le := facts.2.1
    map := J
    domain := U
    open_domain := openU
    contains := fun ε hp hw => (properties ε hp hw).1
    smooth := fun ε hp hw => (properties ε hp hw).2.1
    right := fun ε hp hw => (properties ε hp hw).2.2.1
    left := fun ε hp hw => (properties ε hp hw).2.2.2 }

namespace InverseFamily
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι] {T : M ≃ₜ M} {r : ℝ}
  {F : Maps (E := E) (ι := ι) T r} (d : InverseFamily F)

theorem map_contMDiff (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ d.window) (a : cube (ι := ι) ε) :
    ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (fun y => d.map ε (a.val,y)) := by
  exact (d.smooth ε hp hw).comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
    (fun _ => ⟨d.contains ε hp hw a.property,mem_univ _⟩)

theorem moving_tendsto
    {A : Type*} (ε : A → ℝ≥0) (controls : ∀ a, cube (ι := ι) (ε a)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ a in l, 0 < ε a)
    (v : A → M) (x : M) (moving : Tendsto v l (𝓝 x)) :
    Tendsto (fun a => d.map (ε a) ((controls a).val,v a)) l (𝓝 (T.symm x)) := by
  apply F.moving_inverse_tendsto ε controls l limit positive
    (fun a y => d.map (ε a) ((controls a).val,y)) ?_ v x moving
  have window : ∀ᶠ a in l, ε a ≤ d.window :=
    (limit.eventually (gt_mem_nhds d.positive)).mono (fun _ h => h.le)
  filter_upwards [positive,window] with a hp hw
  exact d.right (ε a) hp hw _ (d.contains (ε a) hp hw (controls a).property)

end InverseFamily
end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
