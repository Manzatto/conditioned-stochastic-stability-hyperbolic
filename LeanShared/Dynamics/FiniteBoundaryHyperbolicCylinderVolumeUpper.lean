module
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicJacobianLower
public import LeanShared.Dynamics.FiniteBoundaryHyperbolicVolumeUpper

/-! Fixed-radius hyperbolic shooting cylinders have actual volume at most
an arbitrarily small exponential loss divided by the reference unstable
Jacobian product. No cylinder-volume estimate is supplied as a hypothesis. -/
public noncomputable section
namespace LeanShared.FiniteBoundaryHyperbolicTransform.Data
open MeasureTheory MeasureTheory.Measure Set
variable {U S:Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ S]
  [MeasurableSpace (U×S)] [BorelSpace (U×S)]

theorem exists_upper_volume_radius (γ:ℝ) (hγ:1<γ) :
    ∃η:ℝ,0<η ∧ ∀N:ℕ,0<N→∀d:Data U S N,
      (d.k:ℝ)≤1/4→(d.δ:ℝ)≤η→
      ∀μ:Measure (U×S),∀[IsAddHaarMeasure μ],
      ∀B:Set (U×S),MeasurableSet B→
      (∀z∈d.shooting ⁻¹' B,∀i:Fin N,
        DifferentiableAt ℝ (d.nonlinear i) (d.evolve z i.val))→
      ENNReal.ofReal (∏i:Fin N,|(d.expanding i).toLinearMap.det|)*μ (d.shooting ⁻¹' B)≤
        ENNReal.ofReal (γ^N)*μ B := by
  obtain ⟨η,positive,jacobian⟩ := exists_lower_jacobian_radius (U:=U) (S:=S) γ hγ
  refine ⟨η,positive,fun N positiveN d boundK boundDelta μ _ B measurable smooth=>?_⟩
  apply d.reference_volume_le μ B measurable smooth _ _ (pow_nonneg (by linarith) N)
  intro z hz
  exact jacobian N positiveN d boundK boundDelta z (smooth z hz)
end LeanShared.FiniteBoundaryHyperbolicTransform.Data
