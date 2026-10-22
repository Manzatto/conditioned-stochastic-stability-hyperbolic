module

public import LeanShared.Geometry.FiniteNativeTangentCharts
public import LeanShared.Geometry.BundleProjectionCoordinateBounds
public import LeanShared.Dynamics.HyperbolicProjectedBlockBounds

/-! Actual hyperbolic data construct a finite native tangent-chart cover
and one block iterate with arbitrarily small projected coordinate maps in
EVERY valid source/target chart pair. The supplied continuous Riemannian
metric is retained and all frame norm losses are absorbed before N. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

@[expose] def HyperbolicData.chartProjection (h : HyperbolicData (E := E) T Λ) (i : Λ) (x : M) : E →L[ℝ] E :=
  BundleEndomorphismCoordinates.coordinates (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val) h.projection x

@[expose] def HyperbolicData.chartBlock (_h : HyperbolicData (E := E) T Λ)
    (N : ℕ) (i j : Λ) (x : M) : E →L[ℝ] E :=
  BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val) x ((T : M → M)^[N] x)
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[N]) x)

@[expose] def HyperbolicData.chartInverseBlock (_h : HyperbolicData (E := E) T Λ)
    (N : ℕ) (i j : Λ) (x : M) : E →L[ℝ] E :=
  BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val) x ((T.symm : M → M)^[N] x)
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm : M → M)^[N]) x)

set_option maxHeartbeats 1800000 in
theorem HyperbolicData.exists_finite_native_chart_blocks (h : HyperbolicData (E := E) T Λ)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ centers : Finset Λ, ∃ patch : Λ → Set M,
      (∀ i, IsCompact (patch i) ∧ patch i ⊆ (chartAt E i.val).source) ∧
      Λ ⊆ ⋃ i ∈ centers, interior (patch i) ∧
      ∃ N : ℕ, 0 < N ∧
        (∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ Λ,
          x ∈ patch i → (T : M → M)^[N] x ∈ patch j →
          ‖(h.chartBlock N i j x).comp (h.chartProjection i x)‖ ≤ κ) ∧
        (∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ Λ,
          x ∈ patch i → (T.symm : M → M)^[N] x ∈ patch j →
          ‖(h.chartInverseBlock N i j x).comp
            (ContinuousLinearMap.id ℝ E - h.chartProjection i x)‖ ≤ κ) := by
  obtain ⟨centers, patch, C, positiveC, facts, cover, bounds⟩ :=
    FiniteNativeTangentCharts.exists_cover (E := E) Λ h.compact
  obtain ⟨N, positiveN, native⟩ := h.exists_projected_block_bound (κ / C ^ 2) (by positivity)
  have cancel : C ^ 2 * (κ / C ^ 2) = κ := by field_simp
  refine ⟨centers, patch, facts, cover, N, positiveN, ?_, ?_⟩
  · intro i hi j hj x hx source target
    have member : x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).baseSet := by
      rw [TangentChartTrivialization.baseSet]
      exact (facts i).2 source
    have bound := BundleProjectionCocycleCoordinates.map_comp_projection_norm_le
      (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val) h.projection x _ member
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[N]) x)
      C (κ / C ^ 2) positiveC.le (bounds i hi x source).2 (bounds j hj _ target).1 (native x hx).1
    exact bound.trans_eq cancel
  · intro i hi j hj x hx source target
    have member : x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).baseSet := by
      rw [TangentChartTrivialization.baseSet]
      exact (facts i).2 source
    have bound := BundleProjectionCocycleCoordinates.map_comp_projection_norm_le
      (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val)
      (fun x => ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ,E)) x) - h.projection x)
      x _ member (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm : M → M)^[N]) x)
      C (κ / C ^ 2) positiveC.le (bounds i hi x source).2 (bounds j hj _ target).1 (native x hx).2
    rw [BundleProjectionCocycleCoordinates.projection_complement _ _ h.projection x member] at bound
    exact bound.trans_eq cancel

end LeanShared.HyperbolicBasicSet
