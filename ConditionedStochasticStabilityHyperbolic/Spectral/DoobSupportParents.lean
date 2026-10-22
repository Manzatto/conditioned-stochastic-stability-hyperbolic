module

public import LeanShared.Probability.StationaryNoiseParents
public import LeanShared.Dynamics.PositiveCollarPlaqueClosure
public import ConditionedStochasticStabilityHyperbolic.Restriction.DoobLocalization
public import ConditionedStochasticStabilityHyperbolic.Spectral.ClosedNoisePositivity
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveEigenfunction

/-! Exact backward parents in the localized product support, derived from
the actual Doob stationary law rather than supplied as a support hypothesis. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ClosedNoisePositivity

open LeanShared LeanShared.RandomMapKernel LeanShared.WeightedConditioning
open AbsorbingMarkovChains

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

/-- Exact parents of the actual product support. The underlying positive
Doob state type may be open and noncompact; its mapped stationary measure
has compact ambient support. -/
theorem product_support_parent (ρ : Measure Ω) [IsFiniteMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K : Set X) (hK : MeasurableSet K)
    (w : X → ℝ) (hw : Measurable w) (R : ℝ)
    [IsSFiniteKernel (normalizedKernel (killed ρ F hF K hK) w R hw)]
    (d : DoobTransform.EigenData (normalizedKernel (killed ρ F hF K hK) w R hw))
    (μ : Measure X) [(μ.withDensity d.weight).Regular]
    (hleft : normalizedKernel (killed ρ F hF K hK) w R hw ∘ₘ μ = d.rate • μ)
    (p : X) (hp : p ∈ (μ.withDensity d.weight).support) :
    ∃ x ∈ (μ.withDensity d.weight).support, ∃ ω : Ω, F (x, ω) = p := by
  let ν := μ.withDensity d.weight
  let η := ν.comap (Subtype.val : d.State → X)
  have hstep : ∀ z : d.State, ∀ᵐ y ∂d.kernel z,
      ∃ ω : Ω, F (z.val, ω) = y.val := by
    intro z
    have hraw := ae_controlled_transition ρ F hF hFc K hK w hw R z.val
    have hlive : ∀ᵐ y ∂d.liveKernel z, ∃ ω : Ω, F (z.val, ω) = y.val := by
      exact (ae_restrict_iff_subtype d.measurableSet_liveSet).1 (ae_restrict_of_ae hraw)
    exact hlive.filter_mono (Restriction.doob_absolutelyContinuous_live d z).ae_le
  apply LeanShared.NoiseEigenmeasureSupport.exists_support_parent_of_stationary_map
    d.kernel η (d.invariant_weightedMeasure μ hleft)
    Subtype.val measurable_subtype_coe ν (Restriction.map_doob_weightedMeasure d μ)
    ν.isClosed_support.isCompact Measure.support_mem_ae_of_regular F hFc hstep p hp

/-- The genuine stationary product measure supplies the compact collar
parents and the positive seed. All controlled zero propagation takes place
in the fixed positive-weight collar. -/
theorem core_positive_of_actual_doob_collar
    (T : X ≃ₜ X) (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F) (zero : Ω)
    (hFzero : ∀ x, F (x, zero) = T x) (V K G : Set X)
    (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : LeanShared.isolatedCore T K ⊆ V)
    (hcoreG : LeanShared.isolatedCore T K ⊆ G)
    (hcover : ∀ p ∈ LeanShared.isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧
      W ⊆ V ∩ G ∧ ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y)
    (htrans : LeanShared.ControlledPlaqueClosure.forwardTransitiveOn T
      (LeanShared.isolatedCore T K))
    (plaque : (ℤ → Ω) → Set X)
    (hlsc : ∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
      ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧
        ∀ k, zn k ∈ plaque (ωn k))
    (hback : ∀ ω : ℤ → Ω, ∀ z ∈ plaque ω, ∃ b : ℕ → X, b 0 = z ∧
      (∀ n, b n ∈ V ∩ G) ∧ ∀ n,
        F (b (n + 1), LeanShared.ControlledPlaqueClosure.backwardNoise ω n) = b n)
    (hcapture : ∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
      (∀ n, F (b (n + 1), LeanShared.ControlledPlaqueClosure.backwardNoise ω n) = b n) →
      (∀ᶠ n : ℕ in atTop, b n ∈ G) → ∃ j : ℕ,
        b j ∈ plaque (LeanShared.ControlledPlaqueClosure.backwardShift ω j))
    (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
    (hwG : ∀ x ∈ K, x ∈ G → 0 < w x)
    [IsSFiniteKernel (normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw)]
    (d : DoobTransform.EigenData
      (normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw))
    (μ : Measure X)
    (hleft : normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw ∘ₘ μ = d.rate • μ)
    (g : X → ℝ) (hgm : Measurable g) (hgc : ContinuousOn g K)
    (hg0 : ∀ x ∈ K, 0 ≤ g x) (hweight : d.weight = fun x => ENNReal.ofReal (g x))
    [IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ g)]
    (l : ℝ) (hright : ∀ x ∈ K,
      (∫ y, g y ∂normalizedKernel (killed ρ F hF K hK.measurableSet) w R hw x) = l * g x)
    (hlocal : (LeanShared.eigenvectorMeasure μ g).support ⊆ V ∩ G) :
    ∀ x ∈ LeanShared.isolatedCore T K, 0 < g x := by
  let ν := LeanShared.eigenvectorMeasure μ g
  have hν : μ.withDensity d.weight = ν := by rw [hweight]; rfl
  let : (μ.withDensity d.weight).Regular := hν.symm ▸ inferInstanceAs ν.Regular
  have hparents : ∀ p ∈ ν.support, ∃ x ∈ ν.support, ∃ ω : Ω, F (x, ω) = p := by
    intro p hp
    rw [← hν] at hp ⊢
    exact product_support_parent ρ F hF hFc K hK.measurableSet w hw R d μ hleft p hp
  have hseed : ∃ p ∈ ν.support, 0 < g p := by
    have has : ∀ᵐ x ∂ν, x ∈ ν.support := Measure.support_mem_ae_of_regular
    have hh := has.and
      (LeanShared.eigenvectorMeasure_ae_pos μ g hgm)
    exact hh.exists
  apply LeanShared.ControlledPlaqueClosure.core_positive_of_collar_plaques
    T F zero hFzero V K G hVK hK hcoreV hcoreG hcover htrans
    plaque hlsc hback hcapture g hgc hg0 _ ν.support hlocal hparents hseed
  intro x hx hxG ω hy hxg
  exact zero_at_controlled_endpoint ρ F hF hFc K V hK hV hVK w hw R hR
    g hgc hg0 l hright hx (hwG x hx hxG) hxg ω hy

/-- Actual live-chain Doob stationarity supplies ambient parents of its
mapped product support, without requiring continuity of the zero extension. -/
theorem mapped_chain_product_support_parent (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (K : Set X) (hK : MeasurableSet K) [CompactSpace K]
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (g : K →ᵇ ℝ) (hg : ∀ x, 0 ≤ g x) (r : ℝ) (hr : 0 < r)
    (hright : ∀ x, ∫ y, g y ∂(RestrictedNoise.chain ρ F hF K hK w hw R hR hwR).killedTransition x
      = r * g x)
    (μ : Measure K)
    (hleft : (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR).killedTransition ∘ₘ μ
      = ENNReal.ofReal r • μ)
    [IsProbabilityMeasure (LeanShared.eigenvectorMeasure μ g)]
    (p : X) (hp : p ∈ ((LeanShared.eigenvectorMeasure μ g).map Subtype.val).support) :
    ∃ x ∈ ((LeanShared.eigenvectorMeasure μ g).map Subtype.val).support,
      ∃ ω : Ω, F (x, ω) = p := by
  let C := RestrictedNoise.chain ρ F hF K hK w hw R hR hwR
  let : IsFiniteKernel C.killedTransition := by
    change IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let d := Restriction.realEigenData C.killedTransition g hg r hr hright
  let ν := (LeanShared.eigenvectorMeasure μ g).map Subtype.val
  let η := (μ.withDensity d.weight).comap (Subtype.val : d.State → K)
  let i : d.State → X := fun x => x.val.val
  have hi : Measurable i := measurable_subtype_coe.comp measurable_subtype_coe
  have hmap : η.map i = ν := by
    change η.map (Subtype.val ∘ Subtype.val) = ν
    rw [← Measure.map_map measurable_subtype_coe measurable_subtype_coe]
    rw [Restriction.map_doob_weightedMeasure d μ]
    rfl
  have hstep : ∀ z : d.State, ∀ᵐ y ∂d.kernel z,
      ∃ ω : Ω, F (i z, ω) = i y := by
    intro z
    have hraw : ∀ᵐ y ∂C.killedTransition z.val, ∃ ω : Ω, F (i z, ω) = y.val := by
      have ha := ae_controlled_transition ρ F hF hFc K hK
        (LeanShared.SubtypeKernel.zeroExtend K w)
        (LeanShared.SubtypeKernel.measurable_zeroExtend K hK w hw) R (i z)
      rw [← LocalPositiveEigenfunction.map_live_killedTransition
        ρ F hF K hK w hw R hR hwR z.val] at ha
      exact (ae_map_iff measurable_subtype_coe.aemeasurable
        ((isCompact_range (hFc.comp (continuous_const.prodMk continuous_id))).measurableSet)).mp ha
    have hlive : ∀ᵐ y ∂d.liveKernel z, ∃ ω : Ω, F (i z, ω) = i y :=
      (ae_restrict_iff_subtype d.measurableSet_liveSet).1 (ae_restrict_of_ae hraw)
    exact hlive.filter_mono (Restriction.doob_absolutelyContinuous_live d z).ae_le
  exact LeanShared.NoiseEigenmeasureSupport.exists_support_parent_of_stationary_map
    d.kernel η (d.invariant_weightedMeasure μ hleft) i hi ν hmap
    ν.isClosed_support.isCompact Measure.support_mem_ae_of_regular F hFc hstep p hp

end ConditionedStochasticStabilityHyperbolic.ClosedNoisePositivity
