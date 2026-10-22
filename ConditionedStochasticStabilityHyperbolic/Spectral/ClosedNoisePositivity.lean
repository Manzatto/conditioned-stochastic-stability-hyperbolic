module

public import LeanShared.Dynamics.RandomPlaquePositivity
public import LeanShared.Probability.NoiseAccessibility
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Positivity for actual noise kernels killed on a closed region

Continuity is needed only on the compact survival region. An open live
neighborhood of a controlled endpoint gives an open positive noise event;
no continuity of the zero extension across the survival boundary is used.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace ConditionedStochasticStabilityHyperbolic.ClosedNoisePositivity

open LeanShared LeanShared.RandomMapKernel LeanShared.WeightedConditioning
open LeanShared.NoiseAccessibility LeanShared.NoiseEigenmeasureSupport
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]

/-- Genuine positive controlled endpoints yield positive killed integrals,
although the survival region is closed rather than open. Integrability
follows from continuity on the compact region and finite noise. -/
theorem integral_killed_pos_of_control (ρ : Measure Ω) [IsFiniteMeasure ρ]
    [ρ.IsOpenPosMeasure] (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K)
    (g : X → ℝ) (hgc : ContinuousOn g K) (hg0 : ∀ y ∈ K, 0 ≤ g y)
    (x : X) (ω : Ω) (hyV : F (x, ω) ∈ V) (hyg : 0 < g (F (x, ω))) :
    0 < ∫ y, g y ∂killed ρ F hF K hK.measurableSet x := by
  let ν := transition ρ F hF x
  have hgi : Integrable g (killed ρ F hF K hK.measurableSet x) := by
    change IntegrableOn g K (ρ.map (fun ω => F (x, ω)))
    exact hgc.integrableOn_compact hK
  have hga : ∀ᵐ y ∂killed ρ F hF K hK.measurableSet x, 0 ≤ g y :=
    (ae_restrict_mem hK.measurableSet).mono hg0
  apply (integral_pos_iff_support_of_nonneg_ae hga hgi).mpr
  have hevent : {y | 0 < g y} ∈ 𝓝[K] (F (x, ω)) :=
    (hgc _ (hVK hyV)) (lt_mem_nhds hyg)
  obtain ⟨O, hO, hOg⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hevent
  obtain ⟨W, hWO, hW, hyW⟩ := mem_nhds_iff.mp hO
  have hsub : W ∩ V ⊆ K := fun y hy => hVK hy.2
  have hpos : 0 < killed ρ F hF K hK.measurableSet x (W ∩ V) := by
    change 0 < (ν.restrict K) (W ∩ V)
    rw [Measure.restrict_apply (hW.inter hV).measurableSet, inter_eq_left.mpr hsub]
    exact transition_pos ρ F hF hFc x _ (hW.inter hV) ω ⟨hyW, hyV⟩
  apply hpos.trans_le
  apply measure_mono
  intro y hy
  exact ne_of_gt (hOg ⟨hWO hy.1, hVK hy.2⟩)

/-- Zero propagation from the actual normalized right eigenfunction law.
The eigenvalue need not be positive for this implication. -/
theorem zero_at_controlled_endpoint (ρ : Measure Ω) [IsFiniteMeasure ρ]
    [ρ.IsOpenPosMeasure] (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hVK : V ⊆ K)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (g : X → ℝ) (hgc : ContinuousOn g K) (hg0 : ∀ y ∈ K, 0 ≤ g y)
    (l : ℝ) (heigen : ∀ x ∈ K,
      (∫ y, g y ∂normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw x) = l * g x)
    {x : X} (hxK : x ∈ K) (hxw : 0 < w x) (hxg : g x = 0)
    (ω : Ω) (hyV : F (x, ω) ∈ V) : g (F (x, ω)) = 0 := by
  apply le_antisymm _ (hg0 _ (hVK hyV))
  by_contra hn
  have hpos := integral_killed_pos_of_control ρ F hF hFc K V hK hV hVK
    g hgc hg0 x ω hyV (lt_of_not_ge hn)
  have hscalar : (∫ y, g y ∂normalizedKernel
      (killed ρ F hF K hK.measurableSet) w R hw x) =
      (w x / R) * ∫ y, g y ∂killed ρ F hF K hK.measurableSet x := by
    change (∫ y, g y ∂(ENNReal.ofReal (w x / R) • _)) = _
    rw [integral_smul_measure, ENNReal.toReal_ofReal (div_pos hxw hR).le, smul_eq_mul]
  have hp := mul_pos (div_pos hxw hR) hpos
  rw [← hscalar, heigen x hxK, hxg, mul_zero] at hp
  exact lt_irrefl _ hp

omit [TopologicalSpace Ω] in
/-- Target killing and the nonzero left eigenmeasure law localize the actual
left support to the closed survival region. -/
theorem left_support_subset (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (K : Set X) (hK : IsCompact K)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (μ : Measure X)
    (r : ℝ≥0∞) (hr : r ≠ 0)
    (heigen : normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw ∘ₘ μ = r • μ) :
    μ.support ⊆ K := by
  apply support_subset_of_eigenmeasure _ μ r hr heigen K hK.isClosed
  apply Eventually.of_forall
  intro x
  exact Measure.ae_smul_measure (ae_restrict_mem hK.measurableSet) (ENNReal.ofReal (w x / R))

/-- Compact noise makes the actual map range measurable; its pushforward,
restriction, and departure weighting all preserve almost-everywhere
existence of an exact controlled predecessor. -/
theorem ae_controlled_transition [CompactSpace Ω] (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K : Set X) (hK : MeasurableSet K) (w : X → ℝ) (hw : Measurable w)
    (R : ℝ) (x : X) :
    ∀ᵐ y ∂normalizedKernel (killed ρ F hF K hK) w R hw x,
      ∃ ω : Ω, F (x, ω) = y := by
  have hc : Continuous (fun ω => F (x, ω)) :=
    hFc.comp (continuous_const.prodMk continuous_id)
  have hm : MeasurableSet (range (fun ω => F (x, ω))) :=
    (isCompact_range hc).measurableSet
  have ha := ae_map_mem_range hm (hF.comp measurable_prodMk_left).aemeasurable (μ := ρ)
  exact Measure.ae_smul_measure (ae_restrict_of_ae ha) (ENNReal.ofReal (w x / R))

variable [CompactSpace X] [CompactSpace Ω]

/-- The actual closed-live weighted noise chain satisfies core positivity.
Its right law supplies zero propagation, its left law supplies support and
parents, and normalization supplies the seed. Only product localization and
the stated classical plaque geometry remain inputs to this support step. -/
theorem exists_pos_noise_tolerance_for_actual_core_positivity
    (T : X ≃ₜ X) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
      (F : X × Ω → X) (hF : Measurable F) (zero : Ω),
      Continuous F →
      (∀ x, F (x, zero) = T x) →
      (∀ ω : Ω, ∀ x ∈ K, dist (F (x, ω)) (T x) < δ) →
      (∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
        ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y) →
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
      ∀ (w : X → ℝ) (hw : Measurable w) (R : ℝ), 0 < R →
      (∀ x ∈ K, 0 < w x) →
      ∀ (μ : Measure X), μ.Regular → ∀ r : ℝ≥0∞, r ≠ 0 →
      normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw ∘ₘ μ = r • μ →
      ∀ g : X → ℝ, Measurable g → ContinuousOn g K → (∀ x ∈ K, 0 ≤ g x) →
      ∀ l : ℝ, (∀ x ∈ K,
        (∫ y, g y ∂normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw x) = l * g x) →
      (∫ x, g x ∂μ) = 1 → (eigenvectorMeasure μ g).support ⊆ V →
      ∀ x ∈ isolatedCore T K, 0 < g x := by
  obtain ⟨δ, hδ, hp⟩ := RandomPlaquePositivity.exists_pos_noise_tolerance_for_eigenfunction_positivity
    (Ω := Ω) T V K G hVK hK hG hcoreV hcoreG htrans
  refine ⟨δ, hδ, ?_⟩
  intro ρ _ _ F hF zero hFc hFzero hnoise hcover plaque hlsc hback hcapture
    w hw R hR hwpos μ hμregular r hr hleft g hg hgc hg0 l hright hnorm hlocal
  let : μ.Regular := hμregular
  have hSK := left_support_subset ρ F hF K hK w hw R μ r hr hleft
  apply hp F zero hFc hFzero hnoise hcover plaque hlsc hback hcapture
    (normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw) μ r hr hleft
    Measure.support_mem_ae_of_regular hSK
    (fun x _ => ae_controlled_transition ρ F hF hFc K hK.measurableSet w hw R x)
    g hg hgc hg0
  · intro x hx ω hy hxg
    exact zero_at_controlled_endpoint ρ F hF hFc K V hK hV hVK w hw R hR
      g hgc hg0 l hright hx (hwpos x hx) hxg ω hy
  · exact hnorm
  · exact hlocal

end ConditionedStochasticStabilityHyperbolic.ClosedNoisePositivity
