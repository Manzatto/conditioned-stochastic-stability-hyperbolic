module

public import LeanShared.Dynamics.HyperbolicFiniteNativeChartBlocks
public import LeanShared.Geometry.NativeInverseCocycleBounds
public import LeanShared.Geometry.DiffeomorphismIterates

/-! One constructed finite native tangent atlas and one block length give
all four projected estimates needed for projection comparison, including
the inverses of the actual forward and backward differentials. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

@[expose] def inverseChartMap (S : M ≃ₜ M)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) S)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) S.symm)
    (i j : M) (x : M) : E →L[ℝ] E :=
  BundleProjectionCocycleCoordinates.map (TangentSpace (𝓘(ℝ,E)))
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j)
    (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i) (S x) x
    (DiffeomorphismDifferential.differential S forward inverse x).symm.toContinuousLinearMap

set_option maxHeartbeats 1800000 in
theorem HyperbolicData.exists_finite_inverse_chart_blocks (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ centers : Finset Λ, ∃ patch : Λ → Set M, ∃ C > 0,
      (∀ i, IsCompact (patch i) ∧ patch i ⊆ (chartAt E i.val).source) ∧
      Λ ⊆ ⋃ i ∈ centers, interior (patch i) ∧
      (∀ i ∈ centers, ∀ x ∈ patch i,
        ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).continuousLinearMapAt ℝ x‖ ≤ C ∧
        ‖(trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).symmL ℝ x‖ ≤ C) ∧
      ∃ N : ℕ, 0 < N ∧
        (∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ Λ,
          x ∈ patch i → (T : M → M)^[N] x ∈ patch j →
          ‖(h.chartBlock N i j x).comp (h.chartProjection i x)‖ ≤ κ) ∧
        (∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ Λ,
          x ∈ patch i → (T.symm : M → M)^[N] x ∈ patch j →
          ‖(h.chartInverseBlock N i j x).comp
            (ContinuousLinearMap.id ℝ E - h.chartProjection i x)‖ ≤ κ) ∧
        (∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ Λ,
          x ∈ patch i → (T : M → M)^[N] x ∈ patch j →
          ‖(inverseChartMap (T ^ N) (DiffeomorphismIterates.mdifferentiable_pow T forward N)
            (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N) i.val j.val x).comp
            (ContinuousLinearMap.id ℝ E - h.chartProjection j ((T : M → M)^[N] x))‖ ≤ κ) ∧
        (∀ i ∈ centers, ∀ j ∈ centers, ∀ x ∈ Λ,
          x ∈ patch i → (T.symm : M → M)^[N] x ∈ patch j →
          ‖(inverseChartMap (T ^ N).symm (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N)
            (by simpa only [Homeomorph.symm_symm] using DiffeomorphismIterates.mdifferentiable_pow T forward N)
            i.val j.val x).comp (h.chartProjection j ((T.symm : M → M)^[N] x))‖ ≤ κ) := by
  obtain ⟨centers, patch, C, positiveC, facts, cover, bounds⟩ :=
    FiniteNativeTangentCharts.exists_cover (E := E) Λ h.compact
  obtain ⟨N, positiveN, native⟩ := h.exists_projected_block_bound (κ / C ^ 2) (by positivity)
  have cancel : C ^ 2 * (κ / C ^ 2) = κ := by field_simp
  have preserves : MapsTo T Λ Λ := fun _ hx => h.invariant ▸ mem_image_of_mem T hx
  have inversePreserves : MapsTo T.symm Λ Λ := by
    intro x hx
    rw [← h.invariant] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa only [T.symm_apply_apply] using hy
  have member (i : Λ) (x : M) (inside : x ∈ patch i) :
      x ∈ (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val).baseSet := by
    rw [TangentChartTrivialization.baseSet]
    exact (facts i).2 inside
  refine ⟨centers, patch, C, positiveC, facts, cover, bounds, N, positiveN, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj x hx source target
    exact (BundleProjectionCocycleCoordinates.map_comp_projection_norm_le
      (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val) h.projection x _ (member i x source)
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[N]) x)
      C (κ / C ^ 2) positiveC.le (bounds i hi x source).2 (bounds j hj _ target).1
      (native x hx).1).trans_eq cancel
  · intro i hi j hj x hx source target
    have estimate := BundleProjectionCocycleCoordinates.map_comp_projection_norm_le
      (TangentSpace (𝓘(ℝ,E)))
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) i.val)
      (trivializationAt E (TangentSpace (𝓘(ℝ,E))) j.val)
      (fun x => ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ,E)) x) - h.projection x)
      x _ (member i x source) (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm : M → M)^[N]) x)
      C (κ / C ^ 2) positiveC.le (bounds i hi x source).2 (bounds j hj _ target).1 (native x hx).2
    rw [BundleProjectionCocycleCoordinates.projection_complement _ _ h.projection x (member i x source)] at estimate
    exact estimate.trans_eq cancel
  · intro i hi j hj x hx source target
    have target' : (T ^ N) x ∈ patch j := by simpa only [DiffeomorphismIterates.coe_pow] using target
    have native' := (native ((T ^ N) x) (by
      simpa only [DiffeomorphismIterates.coe_pow] using preserves.iterate N hx)).2
    have estimate := DiffeomorphismDifferential.inverse_coordinate_comp_norm_le (T ^ N)
      (DiffeomorphismIterates.mdifferentiable_pow T forward N)
      (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N) i.val j.val x (member j _ target')
      (fun y => ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ,E)) y) - h.projection y)
      C (κ / C ^ 2) positiveC.le (by positivity)
      (bounds i hi x source).1 (bounds j hj _ target').2
      (by
        change ‖(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T ^ N).symm : M → M) ((T ^ N) x)).comp _‖ ≤ _
        rw [DiffeomorphismIterates.coe_symm_pow]
        exact native')
    rw [BundleProjectionCocycleCoordinates.projection_complement _ _ h.projection _ (member j _ target')] at estimate
    simpa only [inverseChartMap, HyperbolicData.chartProjection, DiffeomorphismIterates.coe_pow] using
      estimate.trans_eq cancel
  · intro i hi j hj x hx source target
    have target' : (T ^ N).symm x ∈ patch j := by
      simpa only [DiffeomorphismIterates.coe_symm_pow] using target
    have native' := (native ((T ^ N).symm x) (by
      simpa only [DiffeomorphismIterates.coe_symm_pow] using inversePreserves.iterate N hx)).1
    have estimate := DiffeomorphismDifferential.inverse_coordinate_comp_norm_le (T ^ N).symm
      (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N)
      (by simpa only [Homeomorph.symm_symm] using DiffeomorphismIterates.mdifferentiable_pow T forward N)
      i.val j.val x (member j _ target') h.projection
      C (κ / C ^ 2) positiveC.le (by positivity)
      (bounds i hi x source).1 (bounds j hj _ target').2
      (by
        have transport (y z : M) (same : y = z)
            (A : TangentSpace (𝓘(ℝ,E)) ((T ^ N).symm x) →L[ℝ] TangentSpace (𝓘(ℝ,E)) y) :
            ‖A‖ = ‖(show TangentSpace (𝓘(ℝ,E)) ((T ^ N).symm x) →L[ℝ] TangentSpace (𝓘(ℝ,E)) z from A)‖ := by
          subst z
          rfl
        have same : (T ^ N).symm.symm ((T ^ N).symm x) = (T : M → M)^[N] ((T ^ N).symm x) := by
          rw [Homeomorph.symm_symm, ← DiffeomorphismIterates.coe_pow]
        rw [transport _ _ same]
        simp only [Homeomorph.symm_symm]
        rw [DiffeomorphismIterates.coe_pow]
        exact native')
    simpa only [inverseChartMap, HyperbolicData.chartProjection, DiffeomorphismIterates.coe_symm_pow] using
      estimate.trans_eq cancel

end LeanShared.HyperbolicBasicSet
