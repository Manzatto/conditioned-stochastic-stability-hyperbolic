module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseWordTarget
public import LeanShared.Geometry.CompactUniformCenteredCharts
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! A single spatial tube and noise window keep every intermediate time of
a finite noisy word inside a prescribed open collar of an invariant compact
set. Both thresholds precede the choice of controls and initial state. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set
open scoped Topology NNReal
open LeanShared.FiniteJetComposition

theorem Maps.exists_finite_collar_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (Λ G : Set M) (compact : IsCompact Λ) (invariant : MapsTo (T : M → M) Λ Λ)
    (openG : IsOpen G) (contains : Λ ⊆ G) (N : ℕ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ j : ℕ, j ≤ N → MapsTo (word (fun n => F.family ε (controls n).val) j)
        (Metric.cthickening radius Λ) G := by
  let U : Set M := ⋂ j : Fin (N + 1), ((T : M → M)^[j.val]) ⁻¹' G
  have openU : IsOpen U := isOpen_iInter_of_finite fun j =>
    openG.preimage (T.continuous.iterate j.val)
  have insideU : Λ ⊆ U := by
    intro x hx
    exact mem_iInter.mpr fun j => contains (invariant.iterate j.val hx)
  obtain ⟨radius,positiveRadius,tubeInside⟩ := compact.exists_cthickening_subset_open openU insideU
  have windows (j : Fin (N + 1)) := F.exists_uniform_word_target j.val
    (Metric.cthickening radius Λ) G compact.cthickening openG
      (fun _ hx => mem_iInter.mp (tubeInside hx) j)
  choose cutoff positiveCutoff targets using windows
  obtain ⟨η,positiveη,common⟩ := LeanShared.CompactUniformCenteredCharts.common_positive
    (Finset.univ : Finset (Fin (N + 1))) (fun j => (cutoff j : ℝ))
      (fun j _ => by exact_mod_cast positiveCutoff j)
  refine ⟨radius,positiveRadius,⟨η,positiveη.le⟩,positiveη,fun ε hp hw controls j hj => ?_⟩
  let index : Fin (N + 1) := ⟨j,by omega⟩
  have localWindow : ε ≤ cutoff index := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr hw).trans (common index (Finset.mem_univ _)))
  exact targets index ε hp localWindow controls

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
