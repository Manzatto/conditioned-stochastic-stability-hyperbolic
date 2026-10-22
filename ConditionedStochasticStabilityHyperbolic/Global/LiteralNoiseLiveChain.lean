module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualNoiseClosedLayer
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainExt

/-! # Exact literal noise chains at the global live-state endpoint

The actual restricted noisy chain equals the constructed live restriction as
an entire canonical absorbing chain. This transfers the literal Option(Aᶜ)
path law, survival and QEM definitions without a supplied endpoint identity.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace ConditionedStochasticStabilityHyperbolic.Global.LiteralNoiseLiveChain
open RestrictedLayerChain
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

theorem actual_local_chain_eq_global_restriction
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (Live K : Set X) (hLive : MeasurableSet Live) (hK : MeasurableSet K) (hKLive : K ⊆ Live)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    RestrictedNoise.chain ρ F hF K hK (fun x : K => w x.val)
      (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val) =
      chain (NoiseKernel.chain ρ F hF Live hLive w hw R hR hwR) K hK := by
  apply canonicalChain_eq_of_killedTransition_eq
  exact ActualNoiseClosedLayer.local_killedTransition_eq_global_layer
    ρ F hF Live K hLive hK hKLive w hw R hR hwR

theorem actual_live_chain_eq_restriction
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (A : Set X) (hA : MeasurableSet A)
    (φ : X → ℝ) (hφ : Measurable φ) (R : ℝ) (hR : 0 < R)
    (hwR : ∀ x, Real.exp (φ x) ≤ R) :
    RestrictedNoise.chain ρ F hF Aᶜ hA.compl (fun x : ↥(Aᶜ) => Real.exp (φ x.val))
      ((Real.measurable_exp.comp hφ).comp measurable_subtype_coe) R hR (fun x => hwR x.val) =
      chain (NoiseKernel.chain ρ F hF Aᶜ hA.compl (fun x => Real.exp (φ x))
        (Real.measurable_exp.comp hφ) R hR hwR) Aᶜ hA.compl :=
  actual_local_chain_eq_global_restriction ρ F hF Aᶜ Aᶜ hA.compl hA.compl
    Subset.rfl (fun x => Real.exp (φ x)) (Real.measurable_exp.comp hφ) R hR hwR

end ConditionedStochasticStabilityHyperbolic.Global.LiteralNoiseLiveChain
