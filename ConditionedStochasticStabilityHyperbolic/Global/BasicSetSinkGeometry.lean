module
public import ConditionedStochasticStabilityHyperbolic.Global.BasicSetBasinDecomposition

/-! A sink in the actual heteroclinic graph has no external backward basin.
This is the first attractor step of the deterministic filtration construction. -/
public noncomputable section
open Set Function Bundle Metric
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.BasicSetSinkGeometry

theorem invariant_excludes_basin {X : Type*} [MetricSpace X]
    (T : X → X) {K L : Set X} (compact : IsCompact L) (closed : IsClosed K)
    (disjoint : Disjoint L K) (invariant : MapsTo T K K) :
    Disjoint K (PaperStableBasin.stableBasin T L) := by
  obtain ⟨δ,positive,separated⟩ := Metric.exists_pos_forall_lt_edist compact closed disjoint
  apply Set.disjoint_left.mpr
  intro x hx basin
  obtain ⟨n,y,hy,close⟩ := PaperStableBasin.metric_approach_of_mem_stableBasin T L x basin δ positive
  have apart := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (edist_ne_top y (T^[n+1] x))).mpr
    (separated y hy _ (invariant.iterate (n+1) hx))
  have lower : δ < dist y (T^[n+1] x) := by
    simpa only [ENNReal.coe_toReal,edist_dist,ENNReal.toReal_ofReal dist_nonneg] using apart
  exact (not_lt_of_ge close.le) (by simpa only [dist_comm] using lower)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

theorem sink_backward_basin {i : Fin D.count} (sink : ∀ j, ¬ D.edge i j) :
    PaperStableBasin.unstableBasin T (D.core i) ⊆ D.core i := by
  intro x past
  by_contra outside
  obtain ⟨j,future⟩ := BasicSetBasinDecomposition.forward D x
  have outsideJ : x∉D.core j := by
    intro member
    by_cases same : i=j
    · exact outside (same.symm ▸ member)
    · have invariant : MapsTo T.symm (D.core j) (D.core j) := by
        intro y hy
        obtain ⟨z,hz,same⟩ := (D.basic j).hyperbolic.invariant.symm ▸ hy
        simpa only [← same,T.symm_apply_apply] using hz
      exact Set.disjoint_left.mp
        (invariant_excludes_basin T.symm (D.basic i).hyperbolic.compact
          (D.basic j).hyperbolic.compact.isClosed (D.disjoint same) invariant) member past
  exact sink j ⟨x,⟨past,outside⟩,⟨future,outsideJ⟩⟩
end ConditionedStochasticStabilityHyperbolic.Global.BasicSetSinkGeometry
