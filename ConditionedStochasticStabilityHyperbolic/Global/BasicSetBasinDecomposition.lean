module
public import ConditionedStochasticStabilityHyperbolic.Global.FiniteNonwanderingBasins

/-! Actual forward/backward basic-set basins cover the compact manifold.
Points outside the nonwandering set realize literal heteroclinic edges. -/
public noncomputable section
open Set Function Bundle
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Global.BasicSetBasinDecomposition

theorem nonwandering_inverse {X : Type*} [MetricSpace X] (T : X ≃ₜ X) :
    Paper.nonwanderingSet (T.symm : X → X) = Paper.nonwanderingSet (T : X → X) := by
  have one (S : X ≃ₜ X) : Paper.nonwanderingSet (S : X → X) ⊆
      Paper.nonwanderingSet (S.symm : X → X) := by
    intro x hx U openU member
    obtain ⟨n,positive,y,hy,hit⟩ := hx U openU member
    refine ⟨n,positive,S^[n] y,hit,?_⟩
    change S.invFun^[n] (S.toFun^[n] y)∈U
    rw [S.left_inv.iterate n y]
    exact hy
  exact Subset.antisymm (by simpa only [Homeomorph.symm_symm] using one T.symm) (one T)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} (D : Paper.SpectralDecomposition (E := E) T)

theorem forward (x : M) : ∃ i, x∈PaperStableBasin.stableBasin T (D.core i) :=
  FiniteNonwanderingBasins.exists_stable_basic T T.continuous D.core
    (fun i => (D.basic i).hyperbolic.compact) (fun i => (D.basic i).nonempty)
    D.disjoint (fun i _x hx => (D.basic i).hyperbolic.invariant ▸ mem_image_of_mem T hx)
    D.covering.symm.subset x

theorem backward (x : M) : ∃ i, x∈PaperStableBasin.unstableBasin T (D.core i) := by
  apply FiniteNonwanderingBasins.exists_stable_basic T.symm T.symm.continuous D.core
    (fun i => (D.basic i).hyperbolic.compact) (fun i => (D.basic i).nonempty) D.disjoint ?_ ?_ x
  · intro i y hy
    obtain ⟨z,hz,same⟩ := (D.basic i).hyperbolic.invariant.symm ▸ hy
    simpa only [← same,T.symm_apply_apply] using hz
  · rw [nonwandering_inverse T]
    exact D.covering.symm.subset

theorem heteroclinic_of_wandering (x : M) (outside : x∉Paper.nonwanderingSet (T : M → M)) :
    ∃ i j, x∈PaperStableBasin.unstableBasin T (D.core i) \ D.core i ∧
      x∈PaperStableBasin.stableBasin T (D.core j) \ D.core j := by
  obtain ⟨i,past⟩ := backward D x
  obtain ⟨j,future⟩ := forward D x
  have outsideCore (k) : x∉D.core k := fun member => outside (D.covering ▸ mem_iUnion.mpr ⟨k,member⟩)
  exact ⟨i,j,⟨past,outsideCore i⟩,⟨future,outsideCore j⟩⟩

theorem heteroclinic_indices_different
    (no_cycles : ∀ i, ¬ Relation.TransGen D.edge i i)
    (x : M) (outside : x∉Paper.nonwanderingSet (T : M → M)) :
    ∃ i j, i≠j ∧ D.edge i j := by
  obtain ⟨i,j,past,future⟩ := heteroclinic_of_wandering D x outside
  have edge : D.edge i j := ⟨x,past,future⟩
  refine ⟨i,j,?_,edge⟩
  intro same
  subst j
  exact no_cycles i (Relation.TransGen.single edge)
end ConditionedStochasticStabilityHyperbolic.Global.BasicSetBasinDecomposition
