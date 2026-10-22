module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ClosedNoisePositivity
public import LeanShared.Probability.WeightedRandomMapKernel

/-!
# Positivity with state-and-noise weights

At a fixed departure point, the actual kernel is an ordinary killed random
map driven by its weighted noise law. Boundedness and strict positivity of
the weight on the compact survival region make that law finite and fully
supported. This supports inverse-map Jacobian weights without assuming a
change-of-variables identity or continuity across the killing boundary.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ConditionedStochasticStabilityHyperbolic.NoiseWeightedPositivity

open LeanShared LeanShared.NoiseEigenmeasureSupport LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]

omit [MetricSpace X] [BorelSpace X] [TopologicalSpace Ω] in
/-- Only a bound at this departure point is needed for finiteness of its
weighted noise law. -/
theorem weighted_law_isFinite (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (W : X × Ω → ℝ) (hW : Measurable W) (x : X) (B : ℝ)
    (hB : ∀ ω, W (x, ω) ≤ B) :
    IsFiniteMeasure (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))) := by
  let Wx : Unit × Ω → ℝ := fun p => W (x, p.2)
  have hWx : Measurable Wx := hW.comp (measurable_const.prodMk measurable_snd)
  exact WeightedRandomMapKernel.weighted_noise_isFinite ρ Wx hWx B (fun _ ω => hB ω) ()

omit [MetricSpace X] [BorelSpace X] in
/-- Strict positivity at this departure point preserves the full support
of its weighted noise law. -/
theorem weighted_law_isOpenPos (ρ : Measure Ω) [ρ.IsOpenPosMeasure]
    (W : X × Ω → ℝ) (hW : Measurable W) (x : X)
    (hpos : ∀ ω, 0 < W (x, ω)) :
    (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))).IsOpenPosMeasure := by
  let Wx : Unit × Ω → ℝ := fun p => W (x, p.2)
  have hWx : Measurable Wx := hW.comp (measurable_const.prodMk measurable_snd)
  exact WeightedRandomMapKernel.weighted_noise_isOpenPos ρ Wx hWx (fun _ ω => hpos ω) ()

omit [MetricSpace X] [BorelSpace X] [TopologicalSpace Ω] in
/-- Exact identification with an ordinary random-map kernel at a fixed
state. The driving law retains the entire noise-dependent weight. -/
theorem killed_eq_weighted_law (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (W : X × Ω → ℝ) (hW : Measurable W) (F : X × Ω → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K) (x : X)
    [IsFiniteMeasure (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω))))] :
    WeightedRandomMapKernel.killed ρ W F K hK x =
      RandomMapKernel.killed (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω))))
        F hF K hK x := by
  change (WeightedRandomMapKernel.transition ρ W F x).restrict K = _
  rw [WeightedRandomMapKernel.transition_apply ρ W hW F hF x]
  rfl

/-- A positive controlled live endpoint gives a positive integral for the
actual noise-weighted killed kernel. -/
theorem integral_killed_pos_of_control (ρ : Measure Ω) [IsFiniteMeasure ρ]
    [ρ.IsOpenPosMeasure] (W : X × Ω → ℝ) (hW : Measurable W)
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K)
    (g : X → ℝ) (hgc : ContinuousOn g K) (hg0 : ∀ y ∈ K, 0 ≤ g y)
    (x : X) (B : ℝ) (hB : ∀ ω, W (x, ω) ≤ B) (hpos : ∀ ω, 0 < W (x, ω))
    (ω : Ω) (hyV : F (x, ω) ∈ V) (hyg : 0 < g (F (x, ω))) :
    0 < ∫ y, g y ∂WeightedRandomMapKernel.killed ρ W F K hK.measurableSet x := by
  let : IsFiniteMeasure (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))) :=
    weighted_law_isFinite ρ W hW x B hB
  let : (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))).IsOpenPosMeasure :=
    weighted_law_isOpenPos ρ W hW x hpos
  rw [killed_eq_weighted_law ρ W hW F hF K hK.measurableSet x]
  exact ClosedNoisePositivity.integral_killed_pos_of_control _ F hF hFc K V hK hV hVK
    g hgc hg0 x ω hyV hyg

/-- The actual weighted right eigenfunction law propagates zeros at all
controlled live endpoints. -/
theorem zero_at_controlled_endpoint (ρ : Measure Ω) [IsFiniteMeasure ρ]
    [ρ.IsOpenPosMeasure] (W : X × Ω → ℝ) (hW : Measurable W)
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K)
    (g : X → ℝ) (hgc : ContinuousOn g K) (hg0 : ∀ y ∈ K, 0 ≤ g y)
    (l : ℝ) (heigen : ∀ x ∈ K,
      (∫ y, g y ∂WeightedRandomMapKernel.killed ρ W F K hK.measurableSet x) = l * g x)
    {x : X} (hxK : x ∈ K) (B : ℝ) (hB : ∀ ω, W (x, ω) ≤ B)
    (hpos : ∀ ω, 0 < W (x, ω)) (hxg : g x = 0)
    (ω : Ω) (hyV : F (x, ω) ∈ V) : g (F (x, ω)) = 0 := by
  apply le_antisymm _ (hg0 _ (hVK hyV))
  by_contra hn
  have hp := integral_killed_pos_of_control ρ W hW F hF hFc K V hK hV hVK
    g hgc hg0 x B hB hpos ω hyV (lt_of_not_ge hn)
  rw [heigen x hxK, hxg, mul_zero] at hp
  exact lt_irrefl _ hp

omit [TopologicalSpace Ω] in
/-- Target killing localizes an actual nonzero left eigenmeasure. -/
theorem left_support_subset (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (W : X × Ω → ℝ) (F : X × Ω → X) (K : Set X) (hK : IsCompact K)
    (μ : Measure X) (r : ℝ≥0∞) (hr : r ≠ 0)
    (heigen : WeightedRandomMapKernel.killed ρ W F K hK.measurableSet ∘ₘ μ = r • μ) :
    μ.support ⊆ K := by
  apply support_subset_of_eigenmeasure _ μ r hr heigen K hK.isClosed
  exact Eventually.of_forall (fun _ => ae_restrict_mem hK.measurableSet)

/-- Compact noise supplies exact controlled endpoints almost everywhere
for the actual noise-weighted transition. -/
theorem ae_controlled_transition [CompactSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (W : X × Ω → ℝ) (hW : Measurable W) (F : X × Ω → X)
    (hF : Measurable F) (hFc : Continuous F) (K : Set X) (hK : MeasurableSet K)
    (x : X) : ∀ᵐ y ∂WeightedRandomMapKernel.killed ρ W F K hK x,
      ∃ ω : Ω, F (x, ω) = y := by
  have hc : Continuous (fun ω => F (x, ω)) := hFc.comp (continuous_const.prodMk continuous_id)
  have hm : MeasurableSet (range (fun ω => F (x, ω))) := (isCompact_range hc).measurableSet
  change ∀ᵐ y ∂(WeightedRandomMapKernel.transition ρ W F x).restrict K, _
  rw [WeightedRandomMapKernel.transition_apply ρ W hW F hF x]
  exact ae_restrict_of_ae (ae_map_mem_range hm (hF.comp measurable_prodMk_left).aemeasurable)

variable [CompactSpace X] [CompactSpace Ω]

/-- Core positivity for the literal noise-dependent weighted kernel. The
weight is only required bounded and strictly positive at departures in `K`.
Neither a Jacobian realization nor an inverse transfer law is presumed. -/
theorem exists_pos_noise_tolerance_for_actual_core_positivity
    (T : X ≃ₜ X) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
      (F : X × Ω → X) (_hF : Measurable F) (zero : Ω),
      Continuous F →
      (∀ x, F (x, zero) = T x) →
      (∀ ω : Ω, ∀ x ∈ K, dist (F (x, ω)) (T x) < δ) →
      (∀ p ∈ isolatedCore T K, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ U ⊆ V ∧
        ∀ y ∈ U, ∃ ω : Ω, F (T.symm p, ω) = y) →
      ∀ plaque : (ℤ → Ω) → Set X,
      (∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
        ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧
          ∀ k, zn k ∈ plaque (ωn k)) →
      (∀ ω : ℤ → Ω, ∀ z ∈ plaque ω, ∃ b : ℕ → X, b 0 = z ∧
        (∀ n, b n ∈ V) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
      (∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
        (∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
        (∀ᶠ n : ℕ in atTop, b n ∈ G) →
          ∃ j : ℕ, b j ∈ plaque (backwardShift ω j)) →
      ∀ (W : X × Ω → ℝ) (_hW : Measurable W) (B : ℝ),
      (∀ x ∈ K, ∀ ω, W (x, ω) ≤ B) → (∀ x ∈ K, ∀ ω, 0 < W (x, ω)) →
      ∀ (μ : Measure X), μ.Regular → ∀ r : ℝ≥0∞, r ≠ 0 →
      WeightedRandomMapKernel.killed ρ W F K hK.measurableSet ∘ₘ μ = r • μ →
      ∀ g : X → ℝ, Measurable g → ContinuousOn g K → (∀ x ∈ K, 0 ≤ g x) →
      ∀ l : ℝ, (∀ x ∈ K,
        (∫ y, g y ∂WeightedRandomMapKernel.killed ρ W F K hK.measurableSet x) = l * g x) →
      (∫ x, g x ∂μ) = 1 → (eigenvectorMeasure μ g).support ⊆ V →
      ∀ x ∈ isolatedCore T K, 0 < g x := by
  obtain ⟨δ, hδ, hp⟩ := RandomPlaquePositivity.exists_pos_noise_tolerance_for_eigenfunction_positivity
    (Ω := Ω) T V K G hVK hK hG hcoreV hcoreG htrans
  refine ⟨δ, hδ, ?_⟩
  intro ρ _ _ F hF zero hFc hFzero hnoise hcover plaque hlsc hback hcapture
    W hW B hB hWpos μ hμregular r hr hleft g hg hgc hg0 l hright hnorm hlocal
  let : μ.Regular := hμregular
  have hSK := left_support_subset ρ W F K hK μ r hr hleft
  apply hp F zero hFc hFzero hnoise hcover plaque hlsc hback hcapture
    (WeightedRandomMapKernel.killed ρ W F K hK.measurableSet) μ r hr hleft
    Measure.support_mem_ae_of_regular hSK
    (fun x _ => ae_controlled_transition ρ W hW F hF hFc K hK.measurableSet x)
    g hg hgc hg0
  · intro x hx ω hy hxg
    exact zero_at_controlled_endpoint ρ W hW F hF hFc K V hK hV hVK
      g hgc hg0 l hright hx B (hB x hx) (hWpos x hx) hxg ω hy
  · exact hnorm
  · exact hlocal

end ConditionedStochasticStabilityHyperbolic.NoiseWeightedPositivity
