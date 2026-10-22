module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicJacobian
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicVolume

/-! A fixed endpoint box supplies actual finite-cylinder volume at least
its endpoint volume divided by γ^N times the reference unstable-Jacobian
product. Both the shooting map and the determinant estimate are proved. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open MeasureTheory MeasureTheory.Measure Set
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ S]
  [MeasurableSpace (U × S)] [BorelSpace (U × S)]

theorem exists_volume_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, 0 < N → ∀ d : Data U S N,
      (d.k : ℝ) ≤ 1 / 4 → (d.δ : ℝ) ≤ η →
      ∀ μ : Measure (U × S), ∀ [IsAddHaarMeasure μ],
      ∀ B : Set (U × S), MeasurableSet B →
      (∀ z ∈ d.shooting ⁻¹' B, ∀ i : Fin N,
        DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val)) →
      μ B ≤ ENNReal.ofReal (γ ^ N * ∏ i : Fin N, |(d.expanding i).toLinearMap.det|) *
        μ (d.shooting ⁻¹' B) := by
  obtain ⟨η, positive, jacobian⟩ := exists_jacobian_radius (U := U) (S := S) γ hγ
  refine ⟨η, positive, fun N hN d hk hδ μ _ B hB smooth => ?_⟩
  apply d.endpoint_volume_le μ B hB smooth
  intro z hz
  exact jacobian N hN d hk hδ z (smooth z hz)

end LeanShared.FiniteBoundaryHyperbolicTransform.Data
