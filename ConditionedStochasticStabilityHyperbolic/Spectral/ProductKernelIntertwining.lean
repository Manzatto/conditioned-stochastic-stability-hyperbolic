module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ProductSpectralRetraction
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The product retraction intertwines the actual independently killed
kernels. Both identities follow from their integral representations and the
auxiliary eigenrelations; spectral comparison is not an input. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
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

include hX hY hXY in
omit [CompactSpace X] [CompactSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- The auxiliary right eigenfunction gives the actual tensor intertwiner. -/
theorem tensorLift_intertwines (g : Y →ᵇ ℝ) (c : ℝ) (hg : PY g = c • g) :
    PXY.comp (tensorLift g) = (tensorLift g).comp (c • PX) := by
  ext f z
  rcases z with ⟨x, y⟩
  change PXY (tensorLift g f) (x, y) = (c * PX f x) * g y
  rw [hXY]
  change (∫ z : X × Y, f z.1 * g z.2 ∂(KX x).prod (KY y)) = _
  rw [integral_prod_mul, ← hX, ← hY, hg]
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
  ring

omit [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
private theorem section_integrable (h : X × Y →ᵇ ℝ) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable (fun x => PY (sectionAt h x)) μ := by
  simpa only [integrableOn_univ, Function.comp_def] using
    (PY.continuous.comp (continuous_sectionAt h)).continuousOn.integrableOn_compact
      (μ := μ) isCompact_univ

include hY hXY in
private theorem product_section (h : X × Y →ᵇ ℝ) (x : X) :
    sectionAt (PXY h) x = ∫ t, PY (sectionAt h t) ∂KX x := by
  have hi := section_integrable PY h (KX x)
  ext y
  change PXY h (x, y) = (∫ t, PY (sectionAt h t) ∂KX x) y
  have hev := (BoundedContinuousFunction.evalCLM ℝ y).integral_comp_comm hi
  change (∫ t, PY (sectionAt h t) y ∂KX x) =
    (∫ t, PY (sectionAt h t) ∂KX x) y at hev
  rw [← hev, hXY, integral_prod h (h.integrable _)]
  apply integral_congr_ae
  exact ae_of_all _ fun t => (hY (sectionAt h t) y).symm

include hX hY hXY in
/-- The auxiliary left eigenfunctional gives the actual partial-mean
intertwiner. The exchange with the integral is a bounded-linear-map identity. -/
theorem partialMean_intertwines (l : (Y →ᵇ ℝ) →L[ℝ] ℝ) (c : ℝ)
    (hl : ∀ f, l (PY f) = c * l f) :
    (partialMean l).comp PXY = (c • PX).comp (partialMean l) := by
  ext h x
  change l (sectionAt (PXY h) x) = c * PX (partialMean l h) x
  rw [product_section KX KY PY PXY hY hXY]
  rw [← l.integral_comp_comm (section_integrable PY h (KX x)), hX,
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => hl (sectionAt h t)

end ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction
