module
public import LeanShared.Analysis.SchwartzKernelBounds
public import LeanShared.Analysis.SchwartzAmbientEnvelopeBound
public import LeanShared.Analysis.ConeFourierBlocks
public import LeanShared.Geometry.BoundedHolderSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! A fixed Schwartz convolution has an actual radial envelope controlled
by the C0 norm of every function supported in a fixed compact set. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction
namespace LeanShared.SchwartzSupportedConvolutionEnvelope
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem exists_bound (k : 𝓢(E,ℂ)) {K : Set E} (compact : IsCompact K) (m : ℕ) :
    ∃ A : ℝ, 0≤A ∧ ∀f : E →ᵇ ℂ, tsupport f⊆K → ∀x : E,
      ‖∫ y,k (x-y)*f y‖ ≤ A*‖f‖*GraphLeafNorm.radialWeight (m : ℝ) x := by
  obtain ⟨D,hD,decay⟩ := SchwartzKernelBounds.exists_uniform_translated_decay k compact m
  refine ⟨D*volume.real K, mul_nonneg hD ENNReal.toReal_nonneg, ?_⟩
  intro f support x
  have restrict : (∫ y in K,k (x-y)*f y) = ∫ y,k (x-y)*f y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have zero : f y=0 := image_eq_zero_of_notMem_tsupport (fun hs => hy (support hs))
      rw [zero,mul_zero])
  have estimate := norm_setIntegral_le_of_norm_le_const (μ:=volume) compact.measure_lt_top
    (f:=fun y => k (x-y)*f y) (C:=D*GraphLeafNorm.radialWeight (m:ℝ) x*‖f‖)
    (fun y hy => by
      rw [norm_mul]
      exact mul_le_mul (decay x y hy) (f.norm_coe_le_norm y) (norm_nonneg _) (mul_nonneg hD (GraphLeafNorm.radialWeight_nonneg _ x)))
  rw [restrict] at estimate
  exact estimate.trans_eq (by ring)
variable {U A : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0≤J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)

/-- Fixed low-frequency blocks obey the actual graph norm uniformly on a compact support. -/
theorem exists_leaf_bound (σ : 𝓢(E,ℂ)) {K : Set E} (compact : IsCompact K) (a : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : 𝓢(E,ℂ)) (v : BoundedHolderSpace.graph E a),
      (∀x, BoundedHolderSpace.physical E a v x=f x) → tsupport f⊆K →
      ‖SchwartzAmbientRealization.realization μ hJ leaves (ConeFourierBlocks.block σ f)‖ ≤ C*‖v‖ := by
  let m := SchwartzAmbientRealization.decayOrder (U:=U)
  obtain ⟨B,hB,envelope⟩ := exists_bound (FourierSchwartzKernel.kernel σ) compact m
  let I : ℝ := ∫u,GraphLeafNorm.radialWeight (m : ℝ) u ∂μ
  refine ⟨B*J*I, mul_nonneg (mul_nonneg hB hJ) (integral_nonneg (fun u => GraphLeafNorm.radialWeight_nonneg _ u)), ?_⟩
  intro f v physical support
  have view : (fun x => BoundedHolderSpace.physical E a v x) = f := funext physical
  have bound := envelope (BoundedHolderSpace.physical E a v) (by simpa only [view] using support)
  have radial (x : E) : ‖ConeFourierBlocks.block σ f x‖ ≤
      (B*‖v‖)*GraphLeafNorm.radialWeight (m : ℝ) x := by
    rw [ConeFourierBlocks.block_apply]
    have actual := bound x
    simp only [physical] at actual
    exact actual.trans (by
      have step := mul_le_mul_of_nonneg_left (BoundedHolderSpace.physical_norm_le E a v) hB
      exact mul_le_mul_of_nonneg_right step (GraphLeafNorm.radialWeight_nonneg _ x))
  have estimate := SchwartzAmbientRealization.norm_le_of_envelope μ hJ leaves
    (ConeFourierBlocks.block σ f) (SchwartzAmbientRealization.decayOrder_gt (U:=U))
    (mul_nonneg hB (norm_nonneg v)) radial
  exact estimate.trans_eq (by dsimp [I]; ring)
end LeanShared.SchwartzSupportedConvolutionEnvelope
