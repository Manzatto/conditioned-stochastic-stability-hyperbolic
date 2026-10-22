module
public import LeanShared.Dynamics.HyperbolicTangentBlockEquivalences
public import LeanShared.Dynamics.BasicSetEuclideanFrames

/-! Actual derivative blocks on fixed Euclidean parameter spaces. Isometric
frames preserve the Riemannian contraction constants exactly. The frames are
pointwise choices; no global continuous tangent trivialization is assumed. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle

private theorem transport_bound
    {P Q H K : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (e : P ≃ₗᵢ[ℝ] H) (f : Q ≃ₗᵢ[ℝ] K) (D : H ≃L[ℝ] K)
    {κ : ℝ} (positive : 0 ≤ κ) (bound : ‖D.toContinuousLinearMap‖ ≤ κ) :
    ‖((e.toContinuousLinearEquiv.trans D).trans
      f.symm.toContinuousLinearEquiv).toContinuousLinearMap‖ ≤ κ := by
  apply ContinuousLinearMap.opNorm_le_bound _ positive
  intro v
  change ‖f.symm (D (e v))‖ ≤ κ * ‖v‖
  rw [f.symm.norm_map]
  exact (D.toContinuousLinearMap.le_opNorm (e v)).trans
    (by simpa only [e.norm_map] using
      mul_le_mul_of_nonneg_right bound (norm_nonneg (e v)))

set_option maxHeartbeats 2400000 in
theorem BasicData.exists_actual_euclidean_blocks
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T)
    (inverse : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) T.symm)
    (κ : ℝ) (positive : 0 < κ) :
    ∃ ds du N : ℕ, ds + du = Module.finrank ℝ E ∧ 0 < N ∧
      ∀ x ∈ Λ,
        ∃ es : EuclideanSpace ℝ (Fin ds) ≃ₗᵢ[ℝ] b.hyperbolic.stable x,
        ∃ fs : EuclideanSpace ℝ (Fin ds) ≃ₗᵢ[ℝ] b.hyperbolic.stable ((T^N) x),
        ∃ eu : EuclideanSpace ℝ (Fin du) ≃ₗᵢ[ℝ] b.hyperbolic.unstable x,
        ∃ fu : EuclideanSpace ℝ (Fin du) ≃ₗᵢ[ℝ] b.hyperbolic.unstable ((T^N) x),
        ∃ S : EuclideanSpace ℝ (Fin ds) ≃L[ℝ] EuclideanSpace ℝ (Fin ds),
        ∃ U : EuclideanSpace ℝ (Fin du) ≃L[ℝ] EuclideanSpace ℝ (Fin du),
          ‖S.toContinuousLinearMap‖ ≤ κ ∧ ‖U.symm.toContinuousLinearMap‖ ≤ κ ∧
          (∀ v, (fs (S v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
            ((T^N : M ≃ₜ M) : M → M) x (es v).val) ∧
          (∀ v, (fu (U v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
            ((T^N : M ≃ₜ M) : M → M) x (eu v).val) ∧
          (∀ v, (eu (U.symm v)).val = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E))
            ((T^N).symm : M → M) ((T^N) x) (fu v).val) := by
  obtain ⟨ds, du, dimension, frames⟩ := b.exists_euclidean_tangent_frames forward inverse
  obtain ⟨N, positiveN, blocks⟩ := b.hyperbolic.exists_actual_tangent_blocks
    forward inverse κ positive
  refine ⟨ds, du, N, dimension, positiveN, fun x hx => ?_⟩
  have preserves : MapsTo T Λ Λ := fun y hy => by
    rw [← b.hyperbolic.invariant]
    exact mem_image_of_mem T hy
  have target : (T^N) x ∈ Λ := by
    rw [DiffeomorphismIterates.coe_pow]
    exact preserves.iterate N hx
  obtain ⟨es⟩ := (frames x hx).1
  obtain ⟨eu⟩ := (frames x hx).2
  obtain ⟨fs⟩ := (frames ((T^N) x) target).1
  obtain ⟨fu⟩ := (frames ((T^N) x) target).2
  obtain ⟨S, U, boundS, boundU, actionS, actionU, actionInv⟩ := blocks x hx
  refine ⟨es, fs, eu, fu,
    (es.toContinuousLinearEquiv.trans S).trans fs.symm.toContinuousLinearEquiv,
    (eu.toContinuousLinearEquiv.trans U).trans fu.symm.toContinuousLinearEquiv,
    transport_bound es fs S positive.le boundS, ?_, ?_, ?_, ?_⟩
  · exact transport_bound fu eu U.symm positive.le boundU
  · intro v
    change (fs (fs.symm (S (es v)))).val = _
    rw [fs.apply_symm_apply]
    exact actionS (es v)
  · intro v
    change (fu (fu.symm (U (eu v)))).val = _
    rw [fu.apply_symm_apply]
    exact actionU (eu v)
  · intro v
    change (eu (eu.symm (U.symm (fu v)))).val = _
    rw [eu.apply_symm_apply]
    exact actionInv (fu v)

end LeanShared.HyperbolicBasicSet
