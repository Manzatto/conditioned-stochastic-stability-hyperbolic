module

public import LeanShared.Analysis.CompactSchwartzHolderBlocks
public import LeanShared.Analysis.CompletedPhysicalConvolutionIdentity
public import LeanShared.Analysis.AmbientLeafIntegralFromNorm

/-! The ordinary little Hölder realization of the actual weighted blocks
retains their physical convolution formula on every supplied graph leaf.
Both its bounded extension and its representation are constructed from the
literal compact supported smooth core. -/

public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap BoundedContinuousFunction ENNReal
namespace LeanShared.CompactHolderPhysicalBlocks
open ConeDyadicSymbols

variable {E U A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (leaves : A → GraphLeafNorm.GraphLeaf U E J)
  {Cp Cm : Set E} (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
  {K : Set E} (compact : IsCompact K) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
  (t : Bool → ℝ) (margin : ∀ sign, t sign ≤ b)

@[expose] def blocks := SchwartzAmbientBlocks.coreMap μ hJ leaves K
  (symbols χ Φ) t (CompactSchwartzHolderBlocks.bounded μ hJ leaves χ Φ compact hb hb1 t margin)

set_option backward.isDefEq.respectTransparency false in
@[expose] def realize :=
  (blocks μ hJ leaves χ Φ compact hb hb1 t margin).extendOfNorm
    (Eₗ := ↥(EuclideanSmoothHolderCore.space compact.closure hb hb1))
    (CompactSchwartzHolderCore.core compact hb hb1)

set_option backward.isDefEq.respectTransparency false in
theorem realize_core (f : SchwartzJetSpace.supportedCore K) :
    realize μ hJ leaves χ Φ compact hb hb1 t margin
      (CompactSchwartzHolderCore.core compact hb hb1 f) =
      blocks μ hJ leaves χ Φ compact hb hb1 t margin f := by
  change (blocks μ hJ leaves χ Φ compact hb hb1 t margin).extendOfNorm
    (Eₗ := ↥(EuclideanSmoothHolderCore.space compact.closure hb hb1))
    (CompactSchwartzHolderCore.core compact hb hb1)
    (CompactSchwartzHolderCore.core compact hb hb1 f) = _
  obtain ⟨C, _hC, bound⟩ := CompactSchwartzHolderBlocks.bound
    μ hJ leaves χ Φ compact hb hb1 t margin
  have estimate : ∀ c, ‖blocks μ hJ leaves χ Φ compact hb hb1 t margin c‖ ≤
      C * ‖CompactSchwartzHolderCore.core compact hb hb1 c‖ := bound _
  apply LinearMap.extendOfNorm_eq
  · exact CompactSchwartzHolderCore.core_dense compact hb hb1
  · exact ⟨C, estimate⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every ordinary input has the same weighted physical convolution on
each leaf as the generating supported Schwartz functions. -/
theorem block_ae
    (f : EuclideanSmoothHolderCore.space compact.closure hb hb1)
    (j : ℕ × Bool) (a : A) :
    realize μ hJ leaves χ Φ compact hb hb1 t margin f j a =ᵐ[(leaves a).measure μ]
      (fun x => SchwartzAmbientBlocks.weight t j *
        (∫ y, FourierSchwartzKernel.kernel (symbols χ Φ j) (x-y) *
          EuclideanSmoothHolderCore.physical compact.closure hb hb1 f y)) := by
  let evaluation : EuclideanSmoothHolderCore.space compact.closure hb hb1 →L[ℂ]
      Lp ℂ 1 ((leaves a).measure μ) :=
    (lp.evalCLM ℂ _ ∞ a).comp ((DyadicCompletion.coordinate j).comp
      (realize μ hJ leaves χ Φ compact hb hb1 t margin))
  apply CompletedPhysicalConvolutionIdentity.represents volume ((leaves a).measure μ)
    (EuclideanSmoothHolderCore.physical compact.closure hb hb1) evaluation
    (CompactSchwartzHolderCore.core compact hb hb1)
    (CompactSchwartzHolderCore.core_dense compact hb hb1)
    (FourierSchwartzKernel.kernel (symbols χ Φ j)) (SchwartzAmbientBlocks.weight t j)
    ?_ f
  intro c
  change realize μ hJ leaves χ Φ compact hb hb1 t margin
    (CompactSchwartzHolderCore.core compact hb hb1 c) j a =ᵐ[_] _
  rw [realize_core]
  exact (SchwartzAmbientBlocks.coreMap_ae μ hJ leaves K (symbols χ Φ) t _ c j a).trans
    (Filter.Eventually.of_forall fun x => by
      simp only [ConeFourierBlocks.block_apply, CompactSchwartzHolderCore.physical_core])

set_option backward.isDefEq.respectTransparency false in
/-- Uniform physical leaf rows control the actual norm of the constructed
ordinary realization, including both the frequency and leaf suprema. -/
theorem norm_le_of_rows
    (f : EuclideanSmoothHolderCore.space compact.closure hb hb1)
    (R : ℝ) (hR : 0 ≤ R)
    (rows : ∀ (j : ℕ × Bool) (a : A),
      ENNReal.ofReal ((2 : ℝ) ^ (t j.2 * j.1)) *
        (∫⁻ x, ‖∫ y, FourierSchwartzKernel.kernel (symbols χ Φ j) (x-y) *
          EuclideanSmoothHolderCore.physical compact.closure hb hb1 f y‖ₑ
          ∂(leaves a).measure μ) ≤ ENNReal.ofReal R) :
    ‖realize μ hJ leaves χ Φ compact hb hb1 t margin f‖ ≤ R := by
  apply lp.norm_le_of_forall_le hR
  intro j
  apply GraphLeafNorm.ambient_norm_le_of_lintegral μ leaves _
    (fun x => SchwartzAmbientBlocks.weight t j *
      (∫ y, FourierSchwartzKernel.kernel (symbols χ Φ j) (x-y) *
        EuclideanSmoothHolderCore.physical compact.closure hb hb1 f y)) R hR
    (block_ae μ hJ leaves χ Φ compact hb hb1 t margin f j)
  intro a
  have coefficient : ‖SchwartzAmbientBlocks.weight t j‖ₑ =
      ENNReal.ofReal ((2 : ℝ) ^ (t j.2 * j.1)) := by
    rw [← ofReal_norm]
    congr 1
    simp only [SchwartzAmbientBlocks.weight, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.rpow_nonneg (by norm_num) _)
  simp_rw [enorm_mul, coefficient]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact rows j a

end LeanShared.CompactHolderPhysicalBlocks
