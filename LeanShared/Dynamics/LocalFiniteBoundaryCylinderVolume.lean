module

public import LeanShared.Dynamics.FiniteBoundaryHyperbolicCylinderVolume
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicTube
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicLocalRegularity

/-! The volume lower estimate for actual local C1 maps. Differentiability
of the radial extension is derived inside the constructed orbit tube. -/
public noncomputable section
namespace LeanShared.LocalFiniteBoundaryCylinderVolume
open MeasureTheory MeasureTheory.Measure Set
open scoped NNReal
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ S]
  [MeasurableSpace (U × S)] [BorelSpace (U × S)]

set_option maxHeartbeats 1600000 in
theorem exists_radius (γ : ℝ) (hγ : 1 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, 0 < N →
      ∀ d : FiniteBoundaryHyperbolicTransform.Data U S N,
      (d.k : ℝ) ≤ 1 / 4 → (d.δ : ℝ) ≤ η →
      ∀ H : Fin N → U × S → U × S, ∀ R : ℝ,
      (∀ i w, ‖w‖ < R → d.map i w = H i w) →
      (∀ i w, ‖w‖ < R → DifferentiableAt ℝ (H i) w) →
      ∀ μ : Measure (U × S), ∀ [IsAddHaarMeasure μ],
      ∀ B : Set (U × S), MeasurableSet B →
      (∀ p ∈ B, ‖p‖ < (1 - (d.k + d.δ : ℝ≥0)) * R) →
      μ B ≤ ENNReal.ofReal (γ ^ N * ∏ i : Fin N, |(d.expanding i).toLinearMap.det|) *
        μ (d.shooting ⁻¹' B) := by
  obtain ⟨η, positive, volume⟩ := FiniteBoundaryHyperbolicTransform.Data.exists_volume_radius
    (U := U) (S := S) γ hγ
  refine ⟨η, positive, fun N hN d hk hδ H R agreement smooth μ _ B hB boundary => ?_⟩
  apply volume N hN d hk hδ μ B hB
  intro z hz i
  have inside := d.shooting_tube z R (boundary (d.shooting z) hz) i.val i.isLt.le
  exact d.nonlinear_differentiableAt_of_agreement i (H i) R (agreement i) _ inside (smooth i _ inside)

end LeanShared.LocalFiniteBoundaryCylinderVolume
