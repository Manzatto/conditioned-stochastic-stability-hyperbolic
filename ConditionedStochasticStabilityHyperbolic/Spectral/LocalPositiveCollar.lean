module

public import ConditionedStochasticStabilityHyperbolic.Spectral.DoobSupportParents

/-! Core positivity for weights allowed to vanish away from a fixed positive
collar. Product localization, support parents and the positive seed are all
constructed from actual geometric and eigenrelations. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.LocalPositiveCollar

open LocalPositiveEigenfunction Restriction LeanShared
open LeanShared.RandomMapKernel LeanShared.WeightedConditioning
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [TopologicalSpace Ω]

structure ForwardCollarPlaqueInputs (T : X ≃ₜ X) (F : X × Ω → X) (V K G : Set X) where
  zero : Ω
  continuous_noise : Continuous F
  zero_noise : ∀ x, F (x, zero) = T x
  local_cover : ∀ p ∈ isolatedCore T K,
    ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∩ G ∧ ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y
  plaque : (ℤ → Ω) → Set X
  lower_semicontinuous : ∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
    ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧ ∀ k, zn k ∈ plaque (ωn k)
  backward_orbit : ∀ ω : ℤ → Ω, ∀ z ∈ plaque ω,
    ∃ b : ℕ → X, b 0 = z ∧ (∀ n, b n ∈ V ∩ G) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n
  capture : ∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
    (∀ n, F (b (n + 1), backwardNoise ω n) = b n) → (∀ᶠ n : ℕ in atTop, b n ∈ G) →
    ∃ j : ℕ, b j ∈ plaque (backwardShift ω j)


variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] [CompactSpace Ω] [MeasurableSpace Ω]

theorem exists_noise_tolerance_for_rankOne_collar_core_positivity
    (T : X ≃ₜ X) (V K G U : Set X) [CompactSpace K]
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hU : IsOpen U)
    (hcoreU : isolatedCore T K ⊆ U) (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T K ⊆ U)
    (hcoreG : isolatedCore T K ⊆ G) (htrans : forwardTransitiveOn T (isolatedCore T K))
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (w : K → ℝ) (hw : Measurable w) (hwG : ∀ x, x.val ∈ G → 0 < w x)
    (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (hF : Measurable F),
      (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
      ForwardCollarPlaqueInputs T F V K G →
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
  obtain ⟨δl, hδl, hlocal⟩ := exists_noise_eigenvectorMeasure_localization
    T K U (V ∩ G) hK hU hcoreU (hUV.trans hVK) hsep
      (fun x hx => ⟨hUV hx, hUG hx⟩) ρ w hw R hR hwR
  refine ⟨δl, hδl, ?_⟩
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
    hclose
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
  have hgaK : ContinuousOn ga K := continuousOn_zeroExtend K d.eigenvector
  have hg0 : ∀ x ∈ K, 0 ≤ ga x := by
    intro x hx
    change 0 ≤ SubtypeKernel.zeroExtend K d.eigenvector (⟨x, hx⟩ : K).val
    rw [SubtypeKernel.zeroExtend_coe]
    exact hg ⟨x, hx⟩
  have hwa0 : ∀ x ∈ K, x ∈ G → 0 < wa x := by
    intro x hx hxG
    change 0 < SubtypeKernel.zeroExtend K w (⟨x, hx⟩ : K).val
    rw [SubtypeKernel.zeroExtend_coe]
    exact hwG ⟨x, hx⟩ hxG
  have hrighta : ∀ x ∈ K, ∫ y, ga y ∂κ x = d.rate * ga x := by
    intro x hx
    have ht := ambient_right_law ρ F hF K hK.measurableSet w hw R hR hwR
      d.eigenvector d.rate hright ⟨x, hx⟩
    have hmatch : ga x = d.eigenvector ⟨x, hx⟩ :=
      SubtypeKernel.zeroExtend_coe K d.eigenvector ⟨x, hx⟩
    rw [hmatch]
    exact ht
  have hloca : (eigenvectorMeasure (μ.map Subtype.val) ga).support ⊆ V ∩ G := by
    rw [← map_eigenvectorMeasure_zeroExtend K hK.measurableSet μ d.eigenvector
      d.eigenvector.continuous.measurable]
    exact hlocV
  have hprob := rankOneKernelMeasure_product_probability C.killedTransition P hP d
  let : IsProbabilityMeasure (eigenvectorMeasure μ d.eigenvector) := hprob
  let ν := eigenvectorMeasure (μ.map Subtype.val) ga
  have hmapν : (eigenvectorMeasure μ d.eigenvector).map Subtype.val = ν :=
    map_eigenvectorMeasure_zeroExtend K hK.measurableSet μ d.eigenvector
      d.eigenvector.continuous.measurable
  let : IsProbabilityMeasure ν := hmapν ▸ inferInstanceAs
    (IsProbabilityMeasure ((eigenvectorMeasure μ d.eigenvector).map Subtype.val))
  have hparent : ∀ p ∈ ν.support, ∃ x ∈ ν.support, ∃ ω : Ω, F (x, ω) = p := by
    intro p hpν
    rw [← hmapν] at hpν ⊢
    exact ClosedNoisePositivity.mapped_chain_product_support_parent
      ρ F hF hp.continuous_noise K hK.measurableSet w hw R hR hwR
      d.eigenvector hg d.rate d.rate_pos hright μ hleft p hpν
  have hseed : ∃ p ∈ ν.support, 0 < ga p := by
    have has : ∀ᵐ x ∂ν, x ∈ ν.support := Measure.support_mem_ae_of_regular
    exact (has.and (eigenvectorMeasure_ae_pos (μ.map Subtype.val) ga hga)).exists
  have hgpos : ∀ x ∈ isolatedCore T K, 0 < ga x := by
    apply core_positive_of_collar_plaques T F hp.zero hp.zero_noise V K G hVK hK
      hcoreV hcoreG hp.local_cover htrans hp.plaque hp.lower_semicontinuous
      hp.backward_orbit hp.capture ga hgaK hg0 _ ν.support hloca hparent hseed
    intro x hx hxG ω hy hxg
    exact ClosedNoisePositivity.zero_at_controlled_endpoint
      ρ F hF hp.continuous_noise K V hK hV hVK wa hwa R hR
      ga hgaK hg0 d.rate hrighta hx (hwa0 x hx hxG) hxg ω hy
  intro x hx
  simpa only [ga, SubtypeKernel.zeroExtend_coe] using hgpos x.val hx


end ConditionedStochasticStabilityHyperbolic.LocalPositiveCollar
