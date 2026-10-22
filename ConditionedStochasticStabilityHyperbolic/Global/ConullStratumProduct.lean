module

public import ConditionedStochasticStabilityHyperbolic.Global.ConullStratumLeadingData

/-!
# Closed dominant product equals the pushed literal-stratum product

The rate factors in the constructed left measure and right function cancel
exactly. The derived closed eigenmeasure boundary nullity then makes the
stratum product push forward to the original closed-layer product. This
identifies the selected global QEM with the produced local physical measure.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal
namespace ConditionedStochasticStabilityHyperbolic.Global.ConullStratumProduct
open ComplexStrongFeller LayerOperators ConullStratumLeadingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U) (hzero : ∀ x, C.killedTransition x Uᶜ = 0)
  (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ))
  (μ : Measure X) [IsFiniteMeasure μ]
  (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)

omit [IsFiniteMeasure μ] in
/-- The literal-stratum product is the pullback of the actual closed
physical product, with exact cancellation of its positive rate factors. -/
theorem stratum_product_eq_comap :
    LeanShared.eigenvectorMeasure (stratumMeasure C hSF U d μ)
      (stratumData C hSF U hU hzero d).eigenvector =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).comap (Subtype.val : U → X) := by
  unfold LeanShared.eigenvectorMeasure stratumMeasure
  rw [withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  have he : (fun y : U => ENNReal.ofReal d.rate •
      ENNReal.ofReal ((stratumData C hSF U hU hzero d).eigenvector y)) =
      fun y : U => ENNReal.ofReal (d.eigenvector y.val) := by
    funext y
    rw [stratumData_vector]
    change ENNReal.ofReal d.rate * ENNReal.ofReal (d.rate⁻¹ * d.eigenvector y.val) = _
    rw [← ENNReal.ofReal_mul d.rate_pos.le, ← mul_assoc, mul_inv_cancel₀ d.rate_pos.ne', one_mul]
  change (μ.comap (Subtype.val : U → X)).withDensity
    (fun y => ENNReal.ofReal d.rate • ENNReal.ofReal ((stratumData C hSF U hU hzero d).eigenvector y)) = _
  rw [he]
  ext S hS
  rw [withDensity_apply _ hS, (MeasurableEmbedding.subtype_coe hU).comap_apply,
    withDensity_apply _ ((MeasurableEmbedding.subtype_coe hU).measurableSet_image' hS)]
  exact setLIntegral_subtype hU S (fun y => ENNReal.ofReal (d.eigenvector y))

include hmean in
/-- The selected actual-stratum product pushes to the original produced
closed-layer physical probability, so local weak stability is inherited. -/
theorem map_stratum_product_eq_closed_product :
    (LeanShared.eigenvectorMeasure (stratumMeasure C hSF U d μ)
      (stratumData C hSF U hU hzero d).eigenvector).map Subtype.val =
        LeanShared.eigenvectorMeasure μ d.eigenvector := by
  rw [stratum_product_eq_comap C hSF U hU hzero d μ,
    map_comap_subtype_coe hU]
  apply Measure.restrict_eq_self_of_ae_mem
  change ∀ᵐ x ∂μ.withDensity (fun y => ENNReal.ofReal (d.eigenvector y)), x ∈ U
  rw [ae_withDensity_iff d.eigenvector.continuous.measurable.ennreal_ofReal]
  filter_upwards [leading_measure_ae_stratum C hSF U hU hzero d μ hmean] with x hx
  exact fun _ => hx

end ConditionedStochasticStabilityHyperbolic.Global.ConullStratumProduct
