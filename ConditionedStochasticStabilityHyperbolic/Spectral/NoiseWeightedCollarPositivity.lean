module

public import ConditionedStochasticStabilityHyperbolic.Spectral.DoobSupportParents
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseWeightedPositivity
public import ConditionedStochasticStabilityHyperbolic.Spectral.LocalPositiveCollar

/-! Noise-dependent weighted core positivity with weights positive only on
a fixed collar. Source killing outside the closed live set gives actual Doob
data without requiring an unbounded inverse weight to have a global bound. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ConditionedStochasticStabilityHyperbolic.NoiseWeightedCollarPositivity

open LeanShared LeanShared.WeightedRandomMapKernel AbsorbingMarkovChains
open LeanShared.ControlledPlaqueClosure

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [CompactSpace Ω]
  [MeasurableSpace Ω]

theorem core_positive_of_actual_weighted_collar
    (T : X ≃ₜ X) (V K G : Set X) (hV : IsOpen V) (hVK : V ⊆ K) (hK : IsCompact K)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K))
    (ρ : Measure Ω) [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F)
    (hp : LocalPositiveCollar.ForwardCollarPlaqueInputs T F V K G)
    (W : X × Ω → ℝ) (hW : Measurable W) (B : ℝ)
    (hB : ∀ x ∈ K, ∀ ω, W (x, ω) ≤ B)
    (hpos : ∀ x ∈ K, x ∈ G → ∀ ω, 0 < W (x, ω))
    (μ : Measure X) [IsFiniteMeasure μ] (r : ℝ) (hr : 0 < r)
    (hleft : killed ρ W F K hK.measurableSet ∘ₘ μ = ENNReal.ofReal r • μ)
    (g : X → ℝ) (hgm : Measurable g) (hgc : ContinuousOn g K)
    (hg0 : ∀ x, 0 ≤ g x)
    (hright : ∀ x ∈ K, ∫ y, g y ∂killed ρ W F K hK.measurableSet x = r * g x)
    (hnorm : ∫ x, g x ∂μ = 1)
    (hlocal : (eigenvectorMeasure μ g).support ⊆ V ∩ G) :
    ∀ x ∈ isolatedCore T K, 0 < g x := by
  classical
  let L := killed ρ W F K hK.measurableSet
  let : IsSFiniteKernel (noise ρ W) := noise_sfinite ρ W
  let : IsSFiniteKernel L := by
    dsimp [L, killed, transition]
    infer_instance
  let J : Kernel X X := Kernel.piecewise hK.measurableSet L 0
  let ga := K.indicator g
  have hga : Measurable ga := hgm.indicator hK.measurableSet
  have hga0 : ∀ x, 0 ≤ ga x := fun x => by
    by_cases hx : x ∈ K
    · simpa [ga, hx] using hg0 x
    · simp [ga, hx]
  have hμK : ∀ᵐ x ∂μ, x ∈ K := by
    have hh := NoiseWeightedPositivity.left_support_subset ρ W F K hK μ
      (ENNReal.ofReal r) (ENNReal.ofReal_ne_zero_iff.mpr hr) hleft
    exact (show ∀ᵐ x ∂μ, x ∈ μ.support from Measure.support_mem_ae_of_regular).mono hh
  have hleftJ : J ∘ₘ μ = ENNReal.ofReal r • μ := by
    rw [← hleft]
    apply Measure.comp_congr
    filter_upwards [hμK] with x hx
    simp [J, Kernel.piecewise_apply, hx, L]
  have hgaeq : ga =ᵐ[μ] g := hμK.mono fun x hx => by simp [ga, hx]
  have hproduct : eigenvectorMeasure μ ga = eigenvectorMeasure μ g := by
    apply withDensity_congr_ae
    exact hgaeq.fun_comp ENNReal.ofReal
  have hgi : Integrable g μ := by
    have hi := hgc.integrableOn_compact hK (μ := μ)
    change Integrable g (μ.restrict K) at hi
    rwa [Measure.restrict_eq_self_of_ae_mem hμK] at hi
  let : IsProbabilityMeasure (eigenvectorMeasure μ g) :=
    eigenvectorMeasure_isProbability μ g hgi hg0 hnorm
  let : IsProbabilityMeasure (eigenvectorMeasure μ ga) := hproduct.symm ▸ inferInstance
  have hJI (x : X) : Integrable ga (J x) := by
    by_cases hx : x ∈ K
    · have hLaw := NoiseWeightedPositivity.weighted_law_isFinite ρ W hW x B (hB x hx)
      let : IsFiniteMeasure (ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))) := hLaw
      have hfinite : IsFiniteMeasure (L x) := by
        rw [show L x = killed ρ W F K hK.measurableSet x from rfl,
          NoiseWeightedPositivity.killed_eq_weighted_law ρ W hW F hF K hK.measurableSet x]
        change IsFiniteMeasure (((ρ.withDensity (fun ω => ENNReal.ofReal (W (x, ω)))).map
          (fun ω => F (x, ω))).restrict K)
        infer_instance
      let : IsFiniteMeasure (L x) := hfinite
      have hi := hgc.integrableOn_compact hK (μ := L x)
      change Integrable g ((L x).restrict K) at hi
      rw [Measure.restrict_eq_self_of_ae_mem (show ∀ᵐ y ∂L x, y ∈ K from
        ae_restrict_mem hK.measurableSet)] at hi
      have heq : ga =ᵐ[L x] g := (ae_restrict_mem hK.measurableSet).mono
        fun y hy => by simp [ga, hy]
      simpa [J, Kernel.piecewise_apply, hx] using hi.congr heq.symm
    · simp [J, Kernel.piecewise_apply, hx]
  have hrightJ (x : X) : ∫ y, ga y ∂J x = r * ga x := by
    by_cases hx : x ∈ K
    · have heq : ga =ᵐ[L x] g := (ae_restrict_mem hK.measurableSet).mono
        fun y hy => by simp [ga, hy]
      simp only [J, Kernel.piecewise_apply, ite_eq_left hx]
      rw [integral_congr_ae heq, hright x hx]
      simp [ga, hx]
    · simp [J, Kernel.piecewise_apply, ga, hx]
  let d : DoobTransform.EigenData J := {
    rate := ENNReal.ofReal r
    rate_ne_zero := ENNReal.ofReal_ne_zero_iff.mpr hr
    rate_ne_top := ENNReal.ofReal_ne_top
    weight := fun x => ENNReal.ofReal (ga x)
    measurable_weight := hga.ennreal_ofReal
    weight_ne_top := fun _ => ENNReal.ofReal_ne_top
    right_eigen := fun x => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hJI x) (ae_of_all _ hga0),
        hrightJ x, ENNReal.ofReal_mul hr.le] }
  have hsteps : ∀ z : d.State, ∀ᵐ y ∂d.kernel z, ∃ ω : Ω, F (z.val, ω) = y.val := by
    intro z
    have hz : z.val ∈ K := by
      by_contra hz
      have hh : ga z.val = 0 := by simp [ga, hz]
      exact z.property (by simp [d, hh])
    have hraw : ∀ᵐ y ∂J z.val, ∃ ω : Ω, F (z.val, ω) = y := by
      simp only [J, Kernel.piecewise_apply, ite_eq_left hz]
      exact NoiseWeightedPositivity.ae_controlled_transition ρ W hW F hF hp.continuous_noise K
        hK.measurableSet z.val
    have hh : ∀ᵐ y ∂d.liveKernel z, ∃ ω : Ω, F (z.val, ω) = y.val :=
      (ae_restrict_iff_subtype d.measurableSet_liveSet).1 (ae_restrict_of_ae hraw)
    exact hh.filter_mono (Restriction.doob_absolutelyContinuous_live d z).ae_le
  let ν := eigenvectorMeasure μ ga
  let η := ν.comap (Subtype.val : d.State → X)
  have hparent : ∀ p ∈ ν.support, ∃ x ∈ ν.support, ∃ ω : Ω, F (x, ω) = p := by
    intro p hpν
    exact LeanShared.NoiseEigenmeasureSupport.exists_support_parent_of_stationary_map
      d.kernel η (d.invariant_weightedMeasure μ hleftJ) Subtype.val measurable_subtype_coe
      ν (Restriction.map_doob_weightedMeasure d μ) ν.isClosed_support.isCompact
      Measure.support_mem_ae_of_regular F hp.continuous_noise hsteps p hpν
  have hseed : ∃ p ∈ ν.support, 0 < g p := by
    have has : ∀ᵐ x ∂ν, x ∈ ν.support := Measure.support_mem_ae_of_regular
    have hag : ∀ᵐ x ∂ν, 0 < g x := by
      rw [show ν = eigenvectorMeasure μ g from hproduct]
      exact eigenvectorMeasure_ae_pos μ g hgm
    exact (has.and hag).exists
  apply core_positive_of_collar_plaques T F hp.zero hp.zero_noise V K G hVK hK hcoreV hcoreG
    hp.local_cover htrans hp.plaque hp.lower_semicontinuous hp.backward_orbit hp.capture
    g hgc (fun x _ => hg0 x) _ ν.support (by simpa only [ν, hproduct] using hlocal) hparent hseed
  intro x hx hxG ω hy hxg
  exact NoiseWeightedPositivity.zero_at_controlled_endpoint ρ W hW F hF hp.continuous_noise
    K V hK hV hVK g hgc (fun y _ => hg0 y) r hright hx B (hB x hx) (hpos x hx hxG) hxg ω hy

end ConditionedStochasticStabilityHyperbolic.NoiseWeightedCollarPositivity
