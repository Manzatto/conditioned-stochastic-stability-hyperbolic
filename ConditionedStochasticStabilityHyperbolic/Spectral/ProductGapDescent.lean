module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ProductKernelIntertwining
public import ConditionedStochasticStabilityHyperbolic.Spectral.Normalization
public import ConditionedStochasticStabilityHyperbolic.Spectral.PositiveEigenmeasure

/-! The actual independently killed product's gap descends to its first
factor. Only the auxiliary eigenpair and a positive leading pairing enter;
the original factor's gap is the conclusion. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology Y]
  (KX : Kernel X X) (KY : Kernel Y Y) [IsFiniteKernel KX] [IsFiniteKernel KY]
  (PX : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (PY : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
  (PXY : (X × Y →ᵇ ℝ) →L[ℝ] (X × Y →ᵇ ℝ))
  (hX : ∀ f x, PX f x = ∫ t, f t ∂KX x)
  (hY : ∀ f y, PY f y = ∫ t, f t ∂KY y)
  (hXY : ∀ f x y, PXY f (x, y) = ∫ z, f z ∂(KX x).prod (KY y))

/-- Stabilization by an independent saddle preserves the rank-one gap.
The two auxiliary maps are constructed, and both intertwinings are proved
from the actual kernel representations. -/
def descend (dy : RankOneSpectralData PY (1 : Y →ᵇ ℝ))
    (dxy : RankOneSpectralData PXY (1 : X × Y →ᵇ ℝ))
    (hmean : 0 < dxy.mean (tensorLift dy.eigenvector (1 : X →ᵇ ℝ))) :
    RankOneSpectralData PX (1 : X →ᵇ ℝ) := by
  let a := tensorLift (X := X) dy.eigenvector
  let b := partialMean (X := X) dy.mean
  have ha := tensorLift_intertwines KX KY PX PY PXY hX hY hXY
    dy.eigenvector dy.rate dy.right_eigenvector
  have hb := partialMean_intertwines KX KY PX PY PXY hX hY hXY
    dy.mean dy.rate dy.left_eigenfunctional
  let d := dxy.retract a b (partialMean_tensorLift dy.mean dy.eigenvector dy.mean_eigenvector)
    ha hb hmean
  exact d.ofRawNormalization dy.rate dy.rate_pos (by
    simp only [smul_smul, inv_mul_cancel₀ dy.rate_pos.ne', one_smul])

variable (dy : RankOneSpectralData PY (1 : Y →ᵇ ℝ))
  (dxy : RankOneSpectralData PXY (1 : X × Y →ᵇ ℝ))
  (hmean : 0 < dxy.mean (tensorLift dy.eigenvector (1 : X →ᵇ ℝ)))

@[simp] theorem descend_mean :
    (descend KX KY PX PY PXY hX hY hXY dy dxy hmean).mean =
      dxy.mean.comp (tensorLift dy.eigenvector) := by
  unfold descend
  rw [RankOneSpectralData.ofRawNormalization_mean]
  rfl

@[simp] theorem descend_eigenvector :
    (descend KX KY PX PY PXY hX hY hXY dy dxy hmean).eigenvector =
      partialMean dy.mean dxy.eigenvector := by
  unfold descend
  rw [RankOneSpectralData.ofRawNormalization_eigenvector]
  rfl

theorem descend_lift_eigenvector :
    tensorLift dy.eigenvector
      (descend KX KY PX PY PXY hX hY hXY dy dxy hmean).eigenvector = dxy.eigenvector := by
  rw [descend_eigenvector]
  exact dxy.retract_lift_eigenvector (tensorLift dy.eigenvector) (partialMean dy.mean)
    (partialMean_tensorLift dy.mean dy.eigenvector dy.mean_eigenvector)
    (tensorLift_intertwines KX KY PX PY PXY hX hY hXY
      dy.eigenvector dy.rate dy.right_eigenvector)
    (partialMean_intertwines KX KY PX PY PXY hX hY hXY
      dy.mean dy.rate dy.left_eigenfunctional) hmean

/-- The descended product probability is exactly the first marginal of the
product-system probability, at the level of every continuous observable. -/
theorem descend_observable_coefficient (f : X →ᵇ ℝ) :
    let d := descend KX KY PX PY PXY hX hY hXY dy dxy hmean
    d.mean (f * d.eigenvector) =
      dxy.mean (f.compContinuous ⟨Prod.fst, continuous_fst⟩ * dxy.eigenvector) := by
  dsimp only
  rw [descend_mean]
  change dxy.mean (tensorLift dy.eigenvector (f * _)) = _
  congr 1
  have he := descend_lift_eigenvector KX KY PX PY PXY hX hY hXY dy dxy hmean
  rw [← he]
  ext z
  rcases z with ⟨x, y⟩
  simp only [tensorLift_apply, BoundedContinuousFunction.mul_apply,
    BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]
  ring

include hY in
omit [CompactSpace X] [CompactSpace Y] [IsFiniteKernel KY] in
/-- The positive pairing needed for descent follows from actual measure
support and positivity of the auxiliary eigenfunction at a supported seed. -/
theorem pairing_positive_of_supported_seed
    (dy : RankOneSpectralData PY (1 : Y →ᵇ ℝ))
    (dxy : RankOneSpectralData PXY (1 : X × Y →ᵇ ℝ))
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (represent : ∀ f, dxy.mean f = ∫ z, f z ∂μ)
    (x : X) (y : Y) (hμ : (x, y) ∈ μ.support) (hy : 0 < dy.eigenvector y) :
    0 < dxy.mean (tensorLift dy.eigenvector (1 : X →ᵇ ℝ)) := by
  have hpos : ∀ f : Y →ᵇ ℝ, (∀ y, 0 ≤ f y) → ∀ y, 0 ≤ PY f y := by
    intro f hf y
    rw [hY]
    exact integral_nonneg hf
  have hg := dy.eigenvector_nonneg_of_positive hpos
  let f := tensorLift dy.eigenvector (1 : X →ᵇ ℝ)
  rw [represent]
  change 0 < ∫ z, f z ∂μ
  apply (integral_pos_iff_support_of_nonneg (fun z => by
    change 0 ≤ 1 * dy.eigenvector z.2
    simpa using hg z.2) (f.integrable μ)).mpr
  have hO : IsOpen {z : X × Y | 0 < f z} :=
    isOpen_lt continuous_const f.continuous
  have hseed : (x, y) ∈ {z : X × Y | 0 < f z} := by
    change 0 < 1 * dy.eigenvector y
    simpa using hy
  have hmass : 0 < μ {z : X × Y | 0 < f z} :=
    (Measure.mem_support_iff_forall (x, y)).mp hμ _ (hO.mem_nhds hseed)
  exact hmass.trans_le (measure_mono (fun z hz => ne_of_gt hz))

end ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction
