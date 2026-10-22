module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# The finite measure representing a positive bounded-continuous functional

On a compact Hausdorff Borel space, Mathlib's Riesz theorem constructs the
actual finite regular measure. Positivity is the mathematical input, rather
than a supplied representing measure.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported

namespace LeanShared.PositiveFunctionalMeasure

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  (ℓ : (X →ᵇ ℝ) →L[ℝ] ℝ)
  (hℓ : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) → 0 ≤ ℓ f)

/-- The actual positive functional on compactly supported continuous tests. -/
def positiveMap : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := ℓ f.toBoundedContinuousFunction
  map_add' f g := by
    have he : (f + g).toBoundedContinuousFunction =
        f.toBoundedContinuousFunction + g.toBoundedContinuousFunction := by ext x; rfl
    rw [he, map_add]
  map_smul' a f := by
    have he : (a • f).toBoundedContinuousFunction = a • f.toBoundedContinuousFunction := by ext x; rfl
    simp only [he, map_smul, RingHom.id_apply]
  monotone' f g hfg := by
    have hh := hℓ (g.toBoundedContinuousFunction - f.toBoundedContinuousFunction)
      (fun x => sub_nonneg.mpr (hfg x))
    rw [map_sub] at hh
    exact sub_nonneg.mp hh

/-- The finite regular measure is constructed by the classical Riesz theorem. -/
def measure : Measure X := RealRMK.rieszMeasure (positiveMap ℓ hℓ)

instance measure_isFinite : IsFiniteMeasure (measure ℓ hℓ) := by
  unfold measure
  infer_instance

instance measure_regular : (measure ℓ hℓ).Regular := by
  unfold measure
  infer_instance

/-- Exact representation for every bounded continuous test. -/
theorem integral_measure (f : X →ᵇ ℝ) : ∫ x, f x ∂measure ℓ hℓ = ℓ f := by
  let fc : C_c(X, ℝ) := ⟨f.toContinuousMap, HasCompactSupport.of_compactSpace _⟩
  have he : fc.toBoundedContinuousFunction = f := by ext x; rfl
  have h := RealRMK.integral_rieszMeasure (positiveMap ℓ hℓ) fc
  change (∫ x, f x ∂measure ℓ hℓ) = ℓ fc.toBoundedContinuousFunction at h
  rwa [he] at h

end LeanShared.PositiveFunctionalMeasure
