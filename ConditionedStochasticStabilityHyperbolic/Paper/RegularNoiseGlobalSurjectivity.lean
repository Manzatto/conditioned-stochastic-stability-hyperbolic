module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseLocalSurjectivity
import all LeanShared.Geometry.CompactUniformCenteredCharts

/-! The actual local image neighborhoods cover the compact manifold and
produce one positive window of surjectivity for all original perturbations. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal

set_option maxHeartbeats 2400000 in
theorem Maps.exists_global_surjectivity_window
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ a : cube (ι := ι) ε,
      Function.Surjective (F.family ε a.val) := by
  classical
  have neighborhoods := F.exists_local_surjectivity_window regularity deterministic inverse
  choose W openW contains window positiveWindow onto using neighborhoods
  have cover : (univ : Set M) ⊆ ⋃ x : M, W x := by
    intro y _
    refine mem_iUnion.mpr ⟨T.symm y,?_⟩
    simpa only [Homeomorph.apply_symm_apply] using contains (T.symm y)
  obtain ⟨centers,covers⟩ := isCompact_univ.elim_finite_subcover W openW cover
  obtain ⟨η,positiveη,common⟩ := LeanShared.CompactUniformCenteredCharts.common_positive centers
    (fun i => (window i : ℝ)) (fun i _ => positiveWindow i)
  refine ⟨⟨η,positiveη.le⟩,positiveη,fun ε hp hw a y => ?_⟩
  obtain ⟨i,hi,member⟩ := mem_iUnion₂.mp (covers (mem_univ y))
  have parameter : ε ≤ window i := NNReal.coe_le_coe.mp
    ((NNReal.coe_le_coe.mpr hw).trans (common i hi))
  exact onto i ε hp parameter a member

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
