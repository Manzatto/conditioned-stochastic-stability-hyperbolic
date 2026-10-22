module

public import ConditionedStochasticStabilityHyperbolic.Global.ConullStratumProduct
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Produced closed-local core support descends to the actual stratum

The leading product's proved conull support makes every retained core point
in the actual stratum a support point of the constructed stratum product.
No literal-stratum support theorem or compactness of the stratum is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ConullStratumSupport
open ComplexStrongFeller ConullStratumLeadingData ConullStratumProduct
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem mem_support_comap_subtype
    (ν : Measure X) (U : Set X) (hU : MeasurableSet U)
    (ha : ∀ᵐ x ∂ν, x ∈ U) (p : U) (hp : p.val ∈ ν.support) :
    p ∈ (ν.comap (Subtype.val : U → X)).support := by
  rw [Measure.support_eq_forall_isOpen] at hp ⊢
  intro V hpV hV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  rw [(MeasurableEmbedding.subtype_coe hU).comap_apply]
  have he : (Subtype.val : U → X) '' (Subtype.val ⁻¹' W) = W ∩ U := by
    rw [image_preimage_eq_inter_range, Subtype.range_coe]
  rw [he]
  have hrestrict := Measure.restrict_eq_self_of_ae_mem ha
  have hh := congrArg (fun μ : Measure X => μ W) hrestrict
  rw [Measure.restrict_apply hW.measurableSet] at hh
  rw [hh]
  exact hp W hpV hW

/-- The produced closed local support result supplies the actual-stratum
core support needed by the selected global QEM assembler. -/
theorem core_point_mem_stratum_product_support
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (U : Set X) (hU : MeasurableSet U) (hzero : ∀ x, C.killedTransition x Uᶜ = 0)
    (d : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ))
    (μ : Measure X) [IsFiniteMeasure μ]
    (hmean : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
    (p : U) (hp : p.val ∈ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    p ∈ (LeanShared.eigenvectorMeasure (stratumMeasure C hSF U d μ)
      (stratumData C hSF U hU hzero d).eigenvector).support := by
  rw [stratum_product_eq_comap C hSF U hU hzero d μ]
  apply mem_support_comap_subtype _ U hU _ p hp
  change ∀ᵐ x ∂μ.withDensity (fun y => ENNReal.ofReal (d.eigenvector y)), x ∈ U
  rw [ae_withDensity_iff d.eigenvector.continuous.measurable.ennreal_ofReal]
  filter_upwards [leading_measure_ae_stratum C hSF U hU hzero d μ hmean] with x hx
  exact fun _ => hx

end ConditionedStochasticStabilityHyperbolic.Global.ConullStratumSupport
