module
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Continuous local density representatives of the same measure agree at
EVERY point of an open set, rather than only almost everywhere. -/
public section
namespace LeanShared.ContinuousDensityUniqueness
open Set MeasureTheory Measure
open scoped ENNReal

theorem eqOn
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (U : Set X) (openU : IsOpen U) (f g : X → ℝ)
    (continuousF : ContinuousOn f U) (continuousG : ContinuousOn g U)
    (nonnegativeF : ∀ x ∈ U, 0 ≤ f x) (nonnegativeG : ∀ x ∈ U, 0 ≤ g x)
    (same : (μ.restrict U).withDensity (fun x => ENNReal.ofReal (f x)) =
      (μ.restrict U).withDensity (fun x => ENNReal.ofReal (g x))) : EqOn f g U := by
  have equal := (withDensity_eq_iff_of_sigmaFinite
    (continuousF.aemeasurable openU.measurableSet).ennreal_ofReal
    (continuousG.aemeasurable openU.measurableSet).ennreal_ofReal).mp same
  have realEqual : f =ᵐ[μ.restrict U] g := by
    filter_upwards [equal,ae_restrict_mem openU.measurableSet] with x hx hmem
    simpa only [ENNReal.toReal_ofReal (nonnegativeF x hmem),
      ENNReal.toReal_ofReal (nonnegativeG x hmem)] using congrArg ENNReal.toReal hx
  exact eqOn_open_of_ae_eq realEqual openU continuousF continuousG

end LeanShared.ContinuousDensityUniqueness
