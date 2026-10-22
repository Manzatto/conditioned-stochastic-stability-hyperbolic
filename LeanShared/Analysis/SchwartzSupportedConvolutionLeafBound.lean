module
public import LeanShared.Analysis.SchwartzSupportedConvolutionEnvelope

/-! A fixed Schwartz convolution is bounded from actual compactly supported
bounded continuous functions to the full graph-leaf L1 supremum norm. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction
namespace LeanShared.SchwartzSupportedConvolutionEnvelope
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {U A : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

/-- Fixed low-frequency blocks obey the actual graph norm uniformly on a compact support. -/
theorem exists_bcf_leaf_bound (σ : 𝓢(E,ℂ)) {K : Set E} (compact : IsCompact K) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : 𝓢(E,ℂ)) (v : E →ᵇ ℂ),
      (∀x, v x=f x) → tsupport f⊆K →
      ‖SchwartzAmbientRealization.realization μ hJ leaves (ConeFourierBlocks.block σ f)‖ ≤ C*‖v‖ := by
  let m := SchwartzAmbientRealization.decayOrder (U:=U)
  obtain ⟨B,hB,envelope⟩ := exists_bound (FourierSchwartzKernel.kernel σ) compact m
  let I : ℝ := ∫u,GraphLeafNorm.radialWeight (m : ℝ) u ∂μ
  refine ⟨B*J*I, mul_nonneg (mul_nonneg hB hJ) (integral_nonneg (fun u => GraphLeafNorm.radialWeight_nonneg _ u)), ?_⟩
  intro f v physical support
  have view : (fun x => v x) = f := funext physical
  have bound := envelope (v) (by simpa only [view] using support)
  have radial (x : E) : ‖ConeFourierBlocks.block σ f x‖ ≤
      (B*‖v‖)*GraphLeafNorm.radialWeight (m : ℝ) x := by
    rw [ConeFourierBlocks.block_apply]
    have actual := bound x
    simp only [physical] at actual
    exact actual
  have estimate := SchwartzAmbientRealization.norm_le_of_envelope μ hJ leaves
    (ConeFourierBlocks.block σ f) (SchwartzAmbientRealization.decayOrder_gt (U:=U))
    (mul_nonneg hB (norm_nonneg v)) radial
  exact estimate.trans_eq (by dsimp [I]; ring)
end LeanShared.SchwartzSupportedConvolutionEnvelope
