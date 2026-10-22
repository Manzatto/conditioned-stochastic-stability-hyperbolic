module
public import LeanShared.Analysis.FourierHolderRadialEnvelope
public import LeanShared.Analysis.SchwartzAmbientEnvelopeBound
public import LeanShared.Analysis.ConeFourierBlocks

/-! Actual dyadically dilated Fourier blocks gain Hölder regularity in the
literal ambient L1 supremum over every supplied graph-leaf family. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction Convolution
namespace LeanShared.FourierHolderLeafBound
open FourierSchwartzKernel
variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

theorem exists_bound (σ : 𝓢(E,ℂ)) (zero : σ 0=0)
    {K : Set E} (compact : IsCompact K) {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : 𝓢(E,ℂ)) (v : BoundedHolderSpace.graph E a),
      (∀x, BoundedHolderSpace.physical E a v x=f x) → tsupport f⊆K →
      ∀r : ℝ, ∀hr : 1≤r,
      ‖SchwartzAmbientRealization.realization μ hJ leaves
        (ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f)‖ ≤
        C*‖v‖*(r^a)⁻¹ := by
  let m := SchwartzAmbientRealization.decayOrder (U:=U)
  obtain ⟨B,hB,envelope⟩ := FourierHolderRadialEnvelope.exists_envelope σ zero compact ha ha1 m
  let I : ℝ := ∫u,GraphLeafNorm.radialWeight (m : ℝ) u ∂μ
  refine ⟨B*J*I, mul_nonneg (mul_nonneg hB hJ) (integral_nonneg (fun u => GraphLeafNorm.radialWeight_nonneg _ u)), ?_⟩
  intro f v physical support r hr
  have view : (fun x => BoundedHolderSpace.physical E a v x) = f := funext physical
  have bound := envelope v (by simpa only [view] using support) r hr
  have actual (x : E) : ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f x =
      ∫ y, kernel (dilateSymbol σ r (by linarith)) y * f (x-y) := by
    rw [ConeFourierBlocks.block, SchwartzMap.convolution_apply, convolution_def]
    rfl
  have radial (x : E) : ‖ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f x‖ ≤
      (B*‖v‖*(r^a)⁻¹)*GraphLeafNorm.radialWeight (m : ℝ) x := by
    rw [actual]
    simpa only [physical] using bound x
  have estimate := SchwartzAmbientRealization.norm_le_of_envelope μ hJ leaves
    (ConeFourierBlocks.block (dilateSymbol σ r (by linarith)) f)
    (SchwartzAmbientRealization.decayOrder_gt (U:=U)) (by positivity) radial
  exact estimate.trans_eq (by dsimp [I]; ring)
end LeanShared.FourierHolderLeafBound
