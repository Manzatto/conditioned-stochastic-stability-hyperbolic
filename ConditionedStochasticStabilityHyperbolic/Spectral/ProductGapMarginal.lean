module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ProductGapDescent
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! The probability produced by the descended gap is the exact first
marginal of the product probability. Core support and weak convergence can
therefore be transferred by the actual coordinate projection. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction
open LeanShared

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopology Y]
  (KX : Kernel X X) (KY : Kernel Y Y) [IsFiniteKernel KX] [IsFiniteKernel KY]
  (PX : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (PY : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
  (PXY : (X × Y →ᵇ ℝ) →L[ℝ] (X × Y →ᵇ ℝ))
  (hX : ∀ f x, PX f x = ∫ t, f t ∂KX x)
  (hY : ∀ f y, PY f y = ∫ t, f t ∂KY y)
  (hXY : ∀ f x y, PXY f (x, y) = ∫ z, f z ∂(KX x).prod (KY y))
  (dy : RankOneSpectralData PY (1 : Y →ᵇ ℝ))
  (dxy : RankOneSpectralData PXY (1 : X × Y →ᵇ ℝ))
  (hmean : 0 < dxy.mean (tensorLift dy.eigenvector (1 : X →ᵇ ℝ)))

local notation "dx" => descend KX KY PX PY PXY hX hY hXY dy dxy hmean

/-- The marginal identity is a consequence of the actual leading pairings,
not a separately supplied compatibility of the two constructed measures. -/
theorem descended_product_eq_first_marginal
    (μ : Measure X) (μxy : Measure (X × Y)) [IsFiniteMeasure μ] [IsFiniteMeasure μxy]
    (represent : ∀ f : X →ᵇ ℝ, (dx).mean f = ∫ x, f x ∂μ)
    (representxy : ∀ f : X × Y →ᵇ ℝ, dxy.mean f = ∫ z, f z ∂μxy)
    (hg : ∀ x, 0 ≤ (dx).eigenvector x) (hgxy : ∀ z, 0 ≤ dxy.eigenvector z) :
    eigenvectorMeasure μ (dx).eigenvector =
      (eigenvectorMeasure μxy dxy.eigenvector).map Prod.fst := by
  have : IsProbabilityMeasure (eigenvectorMeasure μ (dx).eigenvector) :=
    eigenvector_product_isProbability dx μ represent hg
  have : IsProbabilityMeasure (eigenvectorMeasure μxy dxy.eigenvector) :=
    eigenvector_product_isProbability dxy μxy representxy hgxy
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map_of_stronglyMeasurable measurable_fst f.continuous.measurable.stronglyMeasurable,
    integral_eigenvectorMeasure μ (dx).eigenvector (dx).eigenvector.continuous.measurable hg,
    integral_eigenvectorMeasure μxy dxy.eigenvector dxy.eigenvector.continuous.measurable hgxy]
  change (∫ x, (f * (dx).eigenvector) x ∂μ) =
    ∫ z : X × Y, f z.1 * dxy.eigenvector z ∂μxy
  rw [← represent (f * (dx).eigenvector)]
  calc
    _ = dxy.mean (f.compContinuous ⟨Prod.fst, continuous_fst⟩ * dxy.eigenvector) :=
      descend_observable_coefficient KX KY PX PY PXY hX hY hXY dy dxy hmean f
    _ = _ := by
      rw [representxy]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        simp only [BoundedContinuousFunction.mul_apply,
          BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk]


/-- Positivity at one auxiliary core point transfers to the original core. -/
theorem descended_eigenvector_pos (x : X) (y : Y)
    (hy : 0 < dy.eigenvector y) (hxy : 0 < dxy.eigenvector (x, y)) :
    0 < (dx).eigenvector x := by
  have he := congrArg (fun f : X × Y →ᵇ ℝ => f (x, y))
    (descend_lift_eigenvector KX KY PX PY PXY hX hY hXY dy dxy hmean)
  change (dx).eigenvector x * dy.eigenvector y = dxy.eigenvector (x, y) at he
  nlinarith

omit [CompactSpace X] [CompactSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- Continuous coordinate projection sends every supported point to a
supported point. No full support of an ambient reference measure is used. -/
theorem first_mem_support_map (ν : Measure (X × Y)) (x : X) (y : Y)
    (h : (x, y) ∈ ν.support) : x ∈ (ν.map Prod.fst).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro O hxO hO
  rw [Measure.map_apply measurable_fst hO.measurableSet]
  exact ((Measure.mem_support_iff_forall (x, y)).mp h _
    ((hO.preimage continuous_fst).mem_nhds hxO))

omit [CompactSpace X] [CompactSpace Y] in
/-- Exact marginal identities transfer weak convergence for arbitrary
indexed families, without a regularity assumption on the noise laws. -/
theorem tendsto_first_marginal {I : Type*} (l : Filter I)
    (ν : I → ProbabilityMeasure X) (νxy : I → ProbabilityMeasure (X × Y))
    (ν₀ : ProbabilityMeasure X) (νxy₀ : ProbabilityMeasure (X × Y))
    (hmap : ∀ᶠ i in l, (ν i : Measure X) = (νxy i : Measure (X × Y)).map Prod.fst)
    (hmap₀ : (ν₀ : Measure X) = (νxy₀ : Measure (X × Y)).map Prod.fst)
    (hlim : Filter.Tendsto νxy l (𝓝 νxy₀)) : Filter.Tendsto ν l (𝓝 ν₀) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim)
    (f.compContinuous ⟨Prod.fst, continuous_fst⟩)
  have heq : ∀ᶠ i in l,
      (∫ z, f z.1 ∂(νxy i : Measure (X × Y))) = ∫ x, f x ∂(ν i : Measure X) := by
    filter_upwards [hmap] with i hi
    rw [hi, integral_map_of_stronglyMeasurable measurable_fst
      f.continuous.measurable.stronglyMeasurable]
  have heq₀ : (∫ z, f z.1 ∂(νxy₀ : Measure (X × Y))) = ∫ x, f x ∂(ν₀ : Measure X) := by
    rw [hmap₀, integral_map_of_stronglyMeasurable measurable_fst
      f.continuous.measurable.stronglyMeasurable]
  have h' : Filter.Tendsto (fun i => ∫ z, f z.1 ∂(νxy i : Measure (X × Y))) l
      (𝓝 (∫ z, f z.1 ∂(νxy₀ : Measure (X × Y)))) := by
    simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk] using h
  rw [heq₀] at h'
  exact h'.congr' heq

end ConditionedStochasticStabilityHyperbolic.ProductSpectralRetraction
