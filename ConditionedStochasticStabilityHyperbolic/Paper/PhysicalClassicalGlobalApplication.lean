module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualNoiseClosedLayer
public import ConditionedStochasticStabilityHyperbolic.Spectral.SubordinateEigenvectorSpectrum
public import ConditionedStochasticStabilityHyperbolic.Spectral.RawNormalizationIndependence

/-! The per-layer analytic eigenvectors produced by the ordinary physical
factories give the actual global closed-layer spectrum comparisons. Layers may
have different analytic carriers and even different parameter representations;
only their eventual actual global chain must agree. This is a derived assembly
bridge, not a primitive source assumption. -/

public noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalGlobalApplication
open LeanShared Global RestrictedLayerChain ComplexStrongFeller
variable {X Ω I : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Ω]

private theorem raw_transfer_eq_of_kernel_eq {Y : Type*} [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (C D : AbsorbingMarkovChains.CanonicalChain Y)
    (sC : HasStrongFellerKernel C) (sD : HasStrongFellerKernel D)
    (eq : C.killedTransition = D.killedTransition) (R : ℝ) :
    R • transferOperator (𝕜 := ℂ) C sC = R • transferOperator (𝕜 := ℂ) D sD := by
  congr 1
  ext f x
  rw [transferOperator_apply, transferOperator_apply, eq]

/-- Exact actual-kernel identities transfer the individual physical
factories' eigenvectors to the comparison field of the global source array.
No common stable dimension or common analytic Banach space is imposed. -/
theorem eventual_layer_spectrum
    (H : I → Type*) [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (P : ∀ i, ℝ≥0 → H i →L[ℂ] H i) (principal : I → ℝ)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : I → ℝ≥0 → X × Ω → X) (hF : ∀ i ε, Measurable (F i ε))
    (Live : Set X) (hLive : MeasurableSet Live)
    (K : I → Set X) (hK : ∀ i, MeasurableSet (K i)) (hKL : ∀ i, K i ⊆ Live)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain X)
    (actual : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      C ε = NoiseKernel.chain (ρ ε) (F i ε) (hF i ε) Live hLive w hw R hR hwR)
    (eigenvectors : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
          (fun x => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)),
      ∀ f : K i →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ)
          (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
            (fun x => w x.val) (hw.comp measurable_subtype_coe) R hR (fun x => hwR x.val)) sf) f = z • f →
        principal i < ‖z‖ → ∃ v : H i, v ≠ 0 ∧ P i ε v = z • v) :
    ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K i →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ) (chain (C ε) (K i) (hK i))
          (strongFeller (C ε) sf (K i) (hK i))) f = z • f →
        principal i < ‖z‖ → z ∈ spectrum ℂ (P i ε) := by
  intro i
  filter_upwards [actual i, eigenvectors i] with ε ha hv
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
  have eq := raw_transfer_eq_of_kernel_eq L D sl (strongFeller (C ε) sf (K i) (hK i)) hk R
  intro f hf z he hz
  have hel : (R • transferOperator (𝕜 := ℂ) L sl) f = z • f := by
    rw [eq]
    exact he
  exact subordinate_spectrum_of_analytic_eigenvectors (P i ε)
    (R • transferOperator (𝕜 := ℂ) L sl) (principal i) (hv sl) f hf z hel hz

/-- Each stratum may use its own normalization when constructing its
anisotropic model. The global killed process keeps its original normalization;
the unnormalized physical operators agree exactly. -/
theorem eventual_layer_spectrum_with_individual_scales
    (H : I → Type*) [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedSpace ℂ (H i)]
    [∀ i, CompleteSpace (H i)]
    (P : ∀ i, ℝ≥0 → H i →L[ℂ] H i) (principal : I → ℝ)
    (ρ : ℝ≥0 → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (F : I → ℝ≥0 → X × Ω → X) (hF : ∀ i ε, Measurable (F i ε))
    (Live : Set X) (hLive : MeasurableSet Live)
    (K : I → Set X) (hK : ∀ i, MeasurableSet (K i)) (hKL : ∀ i, K i ⊆ Live)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (scale : I → ℝ) (positive : ∀ i, 0 < scale i) (bound : ∀ i x, w x ≤ scale i)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain X)
    (actual : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      C ε = NoiseKernel.chain (ρ ε) (F i ε) (hF i ε) Live hLive w hw R hR hwR)
    (eigenvectors : ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel
        (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
          (fun x => w x.val) (hw.comp measurable_subtype_coe)
          (scale i) (positive i) (fun x => bound i x.val)),
      ∀ f : K i →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        ((scale i) • transferOperator (𝕜 := ℂ)
          (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
            (fun x => w x.val) (hw.comp measurable_subtype_coe)
            (scale i) (positive i) (fun x => bound i x.val)) sf) f = z • f →
        principal i < ‖z‖ → ∃ v : H i, v ≠ 0 ∧ P i ε v = z • v) :
    ∀ i, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
      ∀ sf : HasStrongFellerKernel (C ε), ∀ f : K i →ᵇ ℂ, f ≠ 0 → ∀ z : ℂ,
        (R • transferOperator (𝕜 := ℂ) (chain (C ε) (K i) (hK i))
          (strongFeller (C ε) sf (K i) (hK i))) f = z • f →
        principal i < ‖z‖ → z ∈ spectrum ℂ (P i ε) := by
  apply eventual_layer_spectrum H P principal ρ F hF Live hLive K hK hKL w hw R hR hwR C actual
  intro i
  filter_upwards [eigenvectors i] with ε hv
  intro sf
  let base := RestrictedNoise.liveKernel (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
  have mass : ∀ x, base x univ ≤ 1 :=
    RestrictedNoise.liveKernel_mass_le_one (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
  have si : HasStrongFellerKernel
      (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
        (fun x => w x.val) (hw.comp measurable_subtype_coe)
        (scale i) (positive i) (fun x => bound i x.val)) :=
    RawNormalizationIndependence.strongFeller base _ (hw.comp measurable_subtype_coe)
      mass R (scale i) hR (positive i) (fun x => hwR x.val) (fun x => bound i x.val) sf
  have eq := RawNormalizationIndependence.raw_transfer_eq (𝕜 := ℂ) base
    (fun x => w x.val) (hw.comp measurable_subtype_coe) mass
    (scale i) R (positive i) hR (fun x => bound i x.val) (fun x => hwR x.val) si sf
  change (scale i) • transferOperator (𝕜 := ℂ)
      (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
        (fun x => w x.val) (hw.comp measurable_subtype_coe)
        (scale i) (positive i) (fun x => bound i x.val)) si =
    R • transferOperator (𝕜 := ℂ)
      (RestrictedNoise.chain (ρ ε) (F i ε) (hF i ε) (K i) (hK i)
        (fun x => w x.val) (hw.comp measurable_subtype_coe)
        R hR (fun x => hwR x.val)) sf at eq
  intro f hf z he hz
  apply hv si f hf z _ hz
  rw [eq]
  exact he

end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalGlobalApplication
