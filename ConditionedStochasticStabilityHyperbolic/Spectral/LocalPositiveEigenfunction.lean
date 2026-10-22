module

public import ConditionedStochasticStabilityHyperbolic.Restriction.NoiseDoobLocalization
public import ConditionedStochasticStabilityHyperbolic.Spectral.ClosedNoisePositivity

/-!
# Forward positivity from actual localized rank-one data

The live eigenmeasure and bounded continuous eigenfunction are carried to
the ambient closed-noise formulation. All measure and harmonic equations,
normalization, regularity, and product localization are derived. The named
plaque inputs below contain only the classical controlled-orbit geometry.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BoundedContinuousFunction ENNReal

namespace ConditionedStochasticStabilityHyperbolic.LocalPositiveEigenfunction

open Restriction LeanShared LeanShared.RandomMapKernel LeanShared.WeightedConditioning
open LeanShared.ControlledPlaqueClosure

section Pushforward

variable {Y X : Type*} [MeasurableSpace Y] [MeasurableSpace X]

/-- A genuine one-step kernel inclusion pushes a left eigenmeasure to a
left eigenmeasure; it does not require a coordinate decomposition. -/
theorem map_left_eigenmeasure (L : Kernel Y Y) (M : Kernel X X)
    (ι : Y → X) (hι : Measurable ι)
    (hstep : ∀ y, (L y).map ι = M (ι y)) (μ : Measure Y) (r : ℝ≥0∞)
    (hleft : L ∘ₘ μ = r • μ) : M ∘ₘ μ.map ι = r • μ.map ι := by
  have he : M ∘ₘ μ.map ι = (L ∘ₘ μ).map ι := by
    ext A hA
    rw [Measure.bind_apply hA M.aemeasurable, Measure.map_apply hι hA,
      Measure.bind_apply (hA.preimage hι) L.aemeasurable,
      lintegral_map (M.measurable_coe hA) hι]
    apply lintegral_congr
    intro y
    rw [← hstep y, Measure.map_apply hι hA]
  rw [he, hleft, Measure.map_smul r hι.aemeasurable]

end Pushforward

section ZeroExtension

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- A subtype continuous observable has a continuous-on-live ambient zero
extension, including when its boundary values are nonzero. -/
theorem continuousOn_zeroExtend (K : Set X) (g : K →ᵇ ℝ) :
    ContinuousOn (SubtypeKernel.zeroExtend K g) K := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : K.domRestrict (SubtypeKernel.zeroExtend K g) = g := by
    funext x
    exact SubtypeKernel.zeroExtend_coe K g x
  rw [he]
  exact g.continuous

omit [TopologicalSpace X] in
/-- Normalization passes through the literal inclusion without a global
continuity assertion on the ambient observable. -/
theorem integral_zeroExtend_map (K : Set X) (hK : MeasurableSet K)
    (μ : Measure K) (g : K → ℝ) :
    (∫ x, SubtypeKernel.zeroExtend K g x ∂μ.map Subtype.val) = ∫ y, g y ∂μ := by
  rw [(MeasurableEmbedding.subtype_coe hK).integral_map]
  simp only [SubtypeKernel.zeroExtend_coe]

end ZeroExtension

section NoiseInclusion

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Exact one-step inclusion for the literal weighted live kernel and its
measurable ambient zero-extension realization. -/
theorem map_live_killedTransition (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (K : Set X) (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (x : K) :
    ((RestrictedNoise.chain ρ F hF K hK w hw R hR hwR).killedTransition x).map Subtype.val =
      normalizedKernel (killed ρ F hF K hK) (SubtypeKernel.zeroExtend K w) R
        (SubtypeKernel.measurable_zeroExtend K hK w hw) x.val := by
  have h := RestrictedNoise.map_killedTransition_pow ρ F hF K hK w hw R hR hwR
    (SubtypeKernel.zeroExtend K w) (SubtypeKernel.measurable_zeroExtend K hK w hw)
    (SubtypeKernel.zeroExtend_le K w R hR.le hwR) (SubtypeKernel.zeroExtend_coe K w) 1 x
  simpa only [pow_one, NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition] using h

/-- The ambient right law on live starting points is a consequence of the
literal-subtype right law and the actual kernel inclusion. -/
theorem ambient_right_law (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (K : Set X) (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (g : K → ℝ) (r : ℝ)
    (heigen : ∀ x, ∫ y, g y ∂(RestrictedNoise.chain ρ F hF K hK w hw R hR hwR).killedTransition x =
      r * g x) (x : K) :
    (∫ y, SubtypeKernel.zeroExtend K g y ∂normalizedKernel (killed ρ F hF K hK)
      (SubtypeKernel.zeroExtend K w) R (SubtypeKernel.measurable_zeroExtend K hK w hw) x.val) =
      r * g x := by
  rw [← map_live_killedTransition ρ F hF K hK w hw R hR hwR x,
    (MeasurableEmbedding.subtype_coe hK).integral_map]
  simpa only [SubtypeKernel.zeroExtend_coe] using heigen x

end NoiseInclusion

section Plaques

variable {X Ω : Type*} [MetricSpace X] [TopologicalSpace Ω]

/-- The precise classical plaque/submersion inputs for forward positivity.
No spectral, measure, support, or eigenfunction positivity is a field. -/
structure ForwardPlaqueInputs (T : X ≃ₜ X) (F : X × Ω → X) (V K G : Set X) where
  zero : Ω
  continuous_noise : Continuous F
  zero_noise : ∀ x, F (x, zero) = T x
  local_cover : ∀ p ∈ isolatedCore T K,
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧ ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y
  plaque : (ℤ → Ω) → Set X
  lower_semicontinuous : ∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
    ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧ ∀ k, zn k ∈ plaque (ωn k)
  backward_orbit : ∀ ω : ℤ → Ω, ∀ z ∈ plaque ω,
    ∃ b : ℕ → X, b 0 = z ∧ (∀ n, b n ∈ V) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n
  capture : ∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
    (∀ n, F (b (n + 1), backwardNoise ω n) = b n) → (∀ᶠ n : ℕ in atTop, b n ∈ G) →
    ∃ j : ℕ, b j ∈ plaque (backwardShift ω j)

end Plaques

section Assembly

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

/-- Forward positivity on the isolated core, for the actual full live
operator. The density product is localized internally, using geometric
separation and finite noise-path extinction, and remains a probability
measure. Only the explicit classical plaque inputs are left as background. -/
theorem exists_noise_tolerance_for_rankOne_core_positivity
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (w : K → ℝ) (hw : Measurable w) (hwpos : ∀ x, 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardPlaqueInputs T F V K G →
      let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw R hR hwR
      ∀ (P : (K →ᵇ ℝ) →L[ℝ] (K →ᵇ ℝ)),
      (∀ (f : K →ᵇ ℝ) (x : K), P f x = ∫ y, f y ∂C.killedTransition x) →
      ∀ (d : RankOneSpectralData P (1 : K →ᵇ ℝ)),
      ∃ μ : Measure K, IsFiniteMeasure μ ∧
        (∀ f : K →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ) ∧
        IsProbabilityMeasure (eigenvectorMeasure μ d.eigenvector) ∧
        (eigenvectorMeasure μ d.eigenvector).support ⊆ retainedRegion K U ∧
        ∀ x : K, x.val ∈ isolatedCore T K → 0 < d.eigenvector x := by
  have hcoreV : isolatedCore T K ⊆ V := hcoreU.trans (subset_closure.trans hUV)
  obtain ⟨δp, hδp, hpos⟩ := ClosedNoisePositivity.exists_pos_noise_tolerance_for_actual_core_positivity
    (Ω := Ω) T V K G hV hVK hK hG hcoreV hcoreG htrans
  obtain ⟨δl, hδl, hlocal⟩ := exists_noise_eigenvectorMeasure_localization
    T K U V hK hU hcoreU (hUV.trans hVK) hsep hUV ρ w hw R hR hwR
  refine ⟨min δp δl, lt_min hδp hδl, ?_⟩
  intro F hF hclose hp
  dsimp only
  intro P hP d
  let C := RestrictedNoise.chain ρ F hF K hK.measurableSet w hw R hR hwR
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let μ := rankOneKernelMeasure C.killedTransition P hP d
  have hm (f : K →ᵇ ℝ) : d.mean f = ∫ y, f y ∂μ :=
    d.eigenmeasure_represents (representedTransfer_positive C.killedTransition P hP) f
  obtain ⟨hg, hright, hleft⟩ := rankOneKernelMeasure_harmonic C.killedTransition P hP d
  have hcloseδl : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δl :=
    fun x hx ω => (hclose x hx ω).trans_le (min_le_right _ _)
  obtain ⟨_hzero, hlocK, _hlocclosure, hlocV⟩ :=
    hlocal F hF hcloseδl d.eigenvector hg d.rate d.rate_pos hright μ hleft
  refine ⟨μ, inferInstance, hm,
    rankOneKernelMeasure_product_probability C.killedTransition P hP d, hlocK, ?_⟩
  let ga := SubtypeKernel.zeroExtend K d.eigenvector
  let wa := SubtypeKernel.zeroExtend K w
  have hga : Measurable ga := SubtypeKernel.measurable_zeroExtend K hK.measurableSet _
    d.eigenvector.continuous.measurable
  have hwa : Measurable wa := SubtypeKernel.measurable_zeroExtend K hK.measurableSet w hw
  let κ := normalizedKernel (killed ρ F hF K hK.measurableSet) wa R hwa
  have hambi : κ ∘ₘ μ.map Subtype.val = ENNReal.ofReal d.rate • μ.map Subtype.val :=
    map_left_eigenmeasure C.killedTransition κ Subtype.val measurable_subtype_coe
      (map_live_killedTransition ρ F hF K hK.measurableSet w hw R hR hwR) μ _ hleft
  have hgaK : ContinuousOn ga K := continuousOn_zeroExtend K d.eigenvector
  have hg0 : ∀ x ∈ K, 0 ≤ ga x := by
    intro x hx
    change 0 ≤ SubtypeKernel.zeroExtend K d.eigenvector (⟨x, hx⟩ : K).val
    rw [SubtypeKernel.zeroExtend_coe]
    exact hg ⟨x, hx⟩
  have hwa0 : ∀ x ∈ K, 0 < wa x := by
    intro x hx
    change 0 < SubtypeKernel.zeroExtend K w (⟨x, hx⟩ : K).val
    rw [SubtypeKernel.zeroExtend_coe]
    exact hwpos ⟨x, hx⟩
  have hrighta : ∀ x ∈ K, ∫ y, ga y ∂κ x = d.rate * ga x := by
    intro x hx
    have ht := ambient_right_law ρ F hF K hK.measurableSet w hw R hR hwR
      d.eigenvector d.rate hright ⟨x, hx⟩
    have hmatch : ga x = d.eigenvector ⟨x, hx⟩ :=
      SubtypeKernel.zeroExtend_coe K d.eigenvector ⟨x, hx⟩
    rw [hmatch]
    exact ht
  have hnorm : ∫ x, ga x ∂μ.map Subtype.val = 1 := by
    rw [integral_zeroExtend_map K hK.measurableSet μ d.eigenvector, ← hm, d.mean_eigenvector]
  have hloca : (eigenvectorMeasure (μ.map Subtype.val) ga).support ⊆ V := by
    rw [← map_eigenvectorMeasure_zeroExtend K hK.measurableSet μ d.eigenvector
      d.eigenvector.continuous.measurable]
    exact hlocV
  have hμregular : (μ.map Subtype.val).Regular := inferInstance
  have hgpos : ∀ x ∈ isolatedCore T K, 0 < ga x :=
    hpos ρ F hF hp.zero hp.continuous_noise hp.zero_noise
      (fun ω x hx => (hclose x hx ω).trans_le (min_le_left _ _)) hp.local_cover
      hp.plaque hp.lower_semicontinuous hp.backward_orbit hp.capture wa hwa R hR hwa0
      (μ.map Subtype.val) hμregular (ENNReal.ofReal d.rate)
      (ENNReal.ofReal_ne_zero_iff.mpr d.rate_pos) hambi ga hga hgaK hg0 d.rate hrighta hnorm hloca
  intro x hx
  simpa only [ga, SubtypeKernel.zeroExtend_coe] using hgpos x.val hx

end Assembly

end ConditionedStochasticStabilityHyperbolic.LocalPositiveEigenfunction
