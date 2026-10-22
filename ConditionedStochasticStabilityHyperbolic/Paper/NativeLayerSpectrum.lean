module
public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalGlobalApplication

/-! The global closed-layer spectrum comparison from local SPECTRUM comparisons. If every eigenvalue
of the normalized local live chain of a layer above the principal rate lies in the spectrum of
the layer's analytic operator, the same holds for the restriction of the actual global chain to
that layer. This is the spectrum-form companion of
`PhysicalClassicalGlobalApplication.eventual_layer_spectrum`; it accepts the output of the
uniform original-weight eigencomparison directly. -/
public noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerSpectrum
open LeanShared Global RestrictedLayerChain ComplexStrongFeller
variable {X Ω I : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Ω]

theorem eventual_layer_spectrum_of_local_spectrum
    (H : I → Type*) [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    (P : ∀ i, ℝ≥0 → H i →L[ℂ] H i) (principal : I → ℝ)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : I → ℝ≥0 → X × Ω → X) (hF : ∀ i ε, Measurable (F i ε))
    (Live : Set X) (hLive : MeasurableSet Live)
    (K : I → Set X) (hK : ∀ i, MeasurableSet (K i)) (hKL : ∀ i, K i ⊆ Live)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain X)
    (actual : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      C ε = NoiseKernel.chain (ρ ε) (F i ε) (hF i ε) Live hLive w hw R hR hwR)
    (local_spectrum : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
          (fun x => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)),
      ∀ f : K i →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ)
          (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
            (fun x => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)) sf) f = z • f →
        principal i < ‖z‖ → z ∈ spectrum ℂ (P i ε)) :
    ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K i →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ) (chain (C ε) (K i) (hK i))
          (strongFeller (C ε) sf (K i) (hK i))) f = z • f →
        principal i < ‖z‖ → z ∈ spectrum ℂ (P i ε) := by
  intro i
  filter_upwards [actual i, local_spectrum i] with ε ha hv
  intro sf
  let L := RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
    (fun x => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)
  let D := chain (C ε) (K i) (hK i)
  have hk : L.killedTransition = D.killedTransition := by
    change L.killedTransition = (chain (C ε) (K i) (hK i)).killedTransition
    rw [ha]
    exact ActualNoiseClosedLayer.local_killedTransition_eq_global_layer
      (ρ ε) (F i ε) (hF i ε) Live (K i) hLive (hK i) (hKL i) w hw R hR hwR
  have sl : HasStrongFellerKernel L := by
    intro f hf hb
    simpa only [hk] using (strongFeller (C ε) sf (K i) (hK i)) f hf hb
  have eq : R • transferOperator (𝕜 := ℂ) L sl =
      R • transferOperator (𝕜 := ℂ) D (strongFeller (C ε) sf (K i) (hK i)) := by
    congr 1
    ext f x
    rw [transferOperator_apply, transferOperator_apply, hk]
  intro f hf z he hz
  have hel : (R • transferOperator (𝕜 := ℂ) L sl) f = z • f := by
    rw [eq]
    exact he
  exact hv sl f hf z hel hz

end ConditionedStochasticStabilityHyperbolic.Paper.NativeLayerSpectrum
