module

public import ConditionedStochasticStabilityHyperbolic.Global.BasicSetSinkGeometry
public import LeanShared.Dynamics.CompactPastTrappingNeighborhood
public import Mathlib.Topology.MetricSpace.Thickening

/-! Actual strict trapping neighborhoods for sinks of the manuscript's
heteroclinic graph. Compact isolated tails approach their isolated core;
the sink property then removes every external backward-trapped point.
The finite-past potential constructs the trapping neighborhood. -/

public noncomputable section
open Set Function Bundle Metric Filter
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.BasicSetSinkTrapping

theorem forwardTrapped_subset_stableBasin {X : Type*} [MetricSpace X]
    (T : X ≃ₜ X) {K : Set X} (compact : IsCompact K)
    (nonempty : (LeanShared.isolatedCore T K).Nonempty) :
    LeanShared.forwardTrapped T K ⊆
      PaperStableBasin.stableBasin T (LeanShared.isolatedCore T K) := by
  intro x hx
  refine ⟨nonempty, Metric.tendsto_atTop.mpr ?_⟩
  intro ε positive
  obtain ⟨N, _positiveN, captured⟩ := LeanShared.exists_pos_stable_tail_subset T compact
    (isOpen_thickening (δ := ε)) (self_subset_thickening positive _)
  refine ⟨N, fun n hn => ?_⟩
  have tail : T^[n] x ∈ T^[N] '' LeanShared.forwardTrapped T K := by
    refine ⟨T^[n - N] x, (LeanShared.mapsTo_forwardTrapped T K).iterate (n-N) hx, ?_⟩
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hn]
  have close := (mem_thickening_iff_infDist_lt nonempty).mp (captured tail)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg infDist_nonneg] using close

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

theorem sink_no_external_past {i : Fin D.count} (sink : ∀ j, ¬ D.edge i j) :
    LeanShared.forwardTrapped T.symm (closure (D.collar i)) ⊆
      LeanShared.isolatedCore T (closure (D.collar i)) := by
  have coreEq : LeanShared.isolatedCore T.symm (closure (D.collar i)) = D.core i := by
    rw [(D.basic i).isolated]
    exact Set.inter_comm _ _
  intro x hx
  have basin := forwardTrapped_subset_stableBasin T.symm isClosed_closure.isCompact
    (coreEq.symm ▸ (D.basic i).nonempty) hx
  rw [coreEq] at basin
  rw [← (D.basic i).isolated]
  exact BasicSetSinkGeometry.sink_backward_basin D sink basin

theorem exists_sink_trapping_neighborhood {i : Fin D.count}
    (sink : ∀ j, ¬ D.edge i j) {O : Set M}
    (openO : IsOpen O) (contains : D.core i ⊆ O) :
    ∃ C : Set M, IsCompact C ∧ D.core i ⊆ interior C ∧
      C ⊆ O ∩ interior (closure (D.collar i)) ∧
      MapsTo T C (interior C) ∧ LeanShared.isolatedCore T C = D.core i := by
  have coreInside : LeanShared.isolatedCore T (closure (D.collar i)) ⊆
      interior (closure (D.collar i)) := by
    rw [← (D.basic i).isolated]
    exact (D.basic i).subset_neighborhood.trans
      (interior_maximal subset_closure (D.basic i).open_neighborhood)
  have nonempty : (closure (D.collar i)).Nonempty :=
    (D.basic i).nonempty.mono ((D.basic i).subset_neighborhood.trans subset_closure)
  obtain ⟨C, compact, containsC, inside, trapping, core⟩ :=
    LeanShared.CompactPastTrappingNeighborhood.exists_neighborhood T
      isClosed_closure.isCompact nonempty coreInside (sink_no_external_past D sink)
      openO (by simpa only [← (D.basic i).isolated] using contains)
  exact ⟨C, compact, by simpa only [← (D.basic i).isolated] using containsC,
    inside, trapping, by simpa only [← (D.basic i).isolated] using core⟩

end ConditionedStochasticStabilityHyperbolic.Global.BasicSetSinkTrapping
