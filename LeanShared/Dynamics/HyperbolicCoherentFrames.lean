module
public import LeanShared.Dynamics.HyperbolicEuclideanBlocks
import all LeanShared.Dynamics.HyperbolicEuclideanBlocks

/-! Actual hyperbolic blocks in a single fixed choice of frames at each
point of the invariant set. Target frames coincide with the next source
frames along every reference orbit. No global continuous trivialization is
assumed; all contraction bounds are independent of the isometric choices. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

@[expose] def HyperbolicData.iteratePoint
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (N : ℕ) (x : Λ) : Λ := by
  refine ⟨(T^N) x.val, ?_⟩
  have preserves : MapsTo T Λ Λ := fun y hy => by
    rw [← h.invariant]
    exact mem_image_of_mem T hy
  rw [DiffeomorphismIterates.coe_pow]
  exact preserves.iterate N x.property

set_option maxHeartbeats 2400000 in
theorem HyperbolicData.exists_blocks_in_coherent_frames
    {E M P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M} (h : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (es : ∀ x : Λ, P ≃ₗᵢ[ℝ] h.stable x.val)
        (eu : ∀ x : Λ, Q ≃ₗᵢ[ℝ] h.unstable x.val) (x : Λ),
        ∃ S : P ≃L[ℝ] P, ∃ U : Q ≃L[ℝ] Q,
          ‖S.toContinuousLinearMap‖ ≤ κ ∧ ‖U.symm.toContinuousLinearMap‖ ≤ κ ∧
          (∀ v, (es (h.iteratePoint N x) (S v)).val =
            mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x.val (es x v).val) ∧
          (∀ v, (eu (h.iteratePoint N x) (U v)).val =
            mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) ((T^N : M ≃ₜ M) : M → M) x.val (eu x v).val) ∧
          (∀ v, (eu x (U.symm v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
            ((T^N).symm : M → M) ((T^N) x.val) (eu (h.iteratePoint N x) v).val) := by
  obtain ⟨N, positiveN, blocks⟩ := h.exists_actual_tangent_blocks forward inverse κ positive
  refine ⟨N, positiveN, fun es eu x => ?_⟩
  obtain ⟨S, U, boundS, boundU, actionS, actionU, actionInv⟩ := blocks x.val x.property
  let fs : P ≃ₗᵢ[ℝ] h.stable ((T^N) x.val) := es (h.iteratePoint N x)
  let fu : Q ≃ₗᵢ[ℝ] h.unstable ((T^N) x.val) := eu (h.iteratePoint N x)
  refine ⟨((es x).toContinuousLinearEquiv.trans S).trans fs.symm.toContinuousLinearEquiv,
    ((eu x).toContinuousLinearEquiv.trans U).trans fu.symm.toContinuousLinearEquiv,
    transport_bound (es x) fs S positive.le boundS,
    transport_bound fu (eu x) U.symm positive.le boundU, ?_, ?_, ?_⟩
  · intro v
    change (fs (fs.symm (S (es x v)))).val = _
    rw [fs.apply_symm_apply]
    exact actionS (es x v)
  · intro v
    change (fu (fu.symm (U (eu x v)))).val = _
    rw [fu.apply_symm_apply]
    exact actionU (eu x v)
  · intro v
    change (eu x ((eu x).symm (U.symm (fu v)))).val = _
    rw [(eu x).apply_symm_apply]
    exact actionInv (fu v)

end LeanShared.HyperbolicBasicSet
