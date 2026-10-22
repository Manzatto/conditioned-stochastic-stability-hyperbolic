module

public import ConditionedStochasticStabilityHyperbolic.Global.NoFullSupportKLFamily
public import ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedPrefixQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.ActualProducedClosedLayerSource
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedKL
public import ConditionedStochasticStabilityHyperbolic.Global.EventualDominantPressureGrowth
public import ConditionedStochasticStabilityHyperbolic.Global.ProducedGlobalHG1Eventually
public import ConditionedStochasticStabilityHyperbolic.Global.ActualFiltrationSelectedQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.LiteralLiveCompleteSpectral

/-! # A selected prefix constructed from produced physical models

Analytic projectors, the physical closed gap, pressure-slack growth of every
subordinate stratum, and the prefix gap/product are constructed in order.
Only ordinary comparison/density/plaque sources remain at the analytic gate;
no physical gap, growth bound, prefix QEM or noisy rate convergence is input.
-/
public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.EventualScaleSelectedPrefix
open LeanShared ShiftedFiltrationGeometry ActualFiltrationGrowth ComplexStrongFeller RestrictedLayerChain
open FiltrationPressureConfinement
open KellerLiverani1999 LocalPositiveCollar Restriction LayerQuasiErgodic
open LeanShared.ControlledPlaqueClosure
variable {X I Ξ Ω Z Zret Core : Type*}
  [NormedAddCommGroup Core] [NormedSpace ℂ Core]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Ξ] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]

local instance compactClosedLayer (T : X ≃ₜ X) (A : Set X) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

open ProducedGlobalHG1Eventually

theorem exists_literal_global_package_from_produced_models
    (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hkℓ : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (hΛ : ∀ i : Fin ℓ, (Λ (D.index i)).Nonempty)
    (E Mid Weak : Fin ℓ → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, Nontrivial (E i)]
    [∀ i, NormedAddCommGroup (Mid i)] [∀ i, NormedSpace ℂ (Mid i)]
    [∀ i, NormedAddCommGroup (Weak i)] [∀ i, NormedSpace ℂ (Weak i)]
    [∀ i, CompleteSpace (Weak i)]
    (pressure : I → ℝ) (hgap : ∀ i : Fin ℓ, i.val < k → i ≠ j → pressure (D.index i) < pressure (D.index j))
    (iH : ∀ i, E i →L[ℂ] Mid i) (iW : ∀ i, E i →L[ℂ] Weak i)
    (law : NNReal → Measure Ξ) (prob : ∀ ε, IsProbabilityMeasure (law ε))
    (generator : ∀ i, NNReal → Ξ → E i →L[ℂ] E i) (scale : Fin ℓ → ℝ)
    (models : ∀ i, ProducedAnnealedModel.Data (iH i) (iW i) law prob (generator i) (scale i))
    (essential : ∀ i, EssentialRadiusContract (E := E i) (W := Weak i))
    (kl : ClassicalContract (E := E j) (W := Weak j))
    (confine : ∀ i, ClassicalConfinementContract (E := E i) (W := Weak i))
    (hdet : ∀ i, spectralRadius ℂ ((scale i : ℂ) • (models i).inputs.operator 0) ≤ ENNReal.ofReal (Real.exp (pressure (D.index i))))
    (hprincipal : ∀ i, (models i).inputs.principal ≤ Real.exp (pressure (D.index i)))
    (det : DeterministicLeading ((models j).inputs.operator 0)) (cutoff margin : ℝ)
    (hαq : (models j).inputs.principal / scale j < cutoff) (hqr : cutoff < det.rate)
    (hqweak : cutoff < (models j).inputs.weakRate / scale j) (hsubq : det.subordinate < cutoff)
    (hmargin : 0 < margin) (hmarginSub : margin < cutoff - det.subordinate)
    (hmarginLead : margin < det.rate - cutoff) (hq : 0 < cutoff)
    (hpressure : scale j * det.rate = Real.exp (pressure (D.index j)))
    (R : ℝ) (hR : 0 < R) (hscaleJ : scale j = R)
    (V G U : Set X) (hV : IsOpen V) (hVK : V ⊆ closedLayer T A Λ ℓ N D j)
    (hU : IsOpen U) (hcoreU : Λ (D.index j) ⊆ U)
    (hUV : closure U ⊆ V) (hUG : closure U ⊆ G)
    (hsep : (T '' closure U) ∩ forwardTrapped T (closedLayer T A Λ ℓ N D j) ⊆ U)
    (hcoreG : Λ (D.index j) ⊆ G) (htrans : forwardTransitiveOn T (Λ (D.index j)))
    (w : X → ℝ) (hw : Measurable w)
    (hwK : Continuous (fun x : closedLayer T A Λ ℓ N D j => w x.val))
    (hwG : ∀ x : closedLayer T A Λ ℓ N D j, x.val ∈ G → 0 < w x.val)
    (hwR : ∀ x, w x ≤ R)
    (ρ : NNReal → Measure Ω) [∀ ε, IsProbabilityMeasure (ρ ε)]
    (hρ : ∀ ε, 0 < ε → (ρ ε).IsOpenPosMeasure)
    (F : NNReal → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
    (hactual : ∀ᶠ ε : NNReal in 𝓝[>] 0, C ε = NoiseKernel.chain (ρ ε) (F ε) (hF ε) Aᶜ hA.measurableSet.compl w hw R hR hwR)
    (hSF : ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε))
    (hnoUp : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε, ∀ i, i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
      (C ε).killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0)
    (hzeroA : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ x, (C ε).killedTransition x A = 0)
    (hUltra : ∀ i, StrongFellerSquareCompact.UltraFellerContract (X := closedLayer T A Λ ℓ N D i))
    (hFredholm : ∀ i, PowerCompactGap.SquareCompactFredholm (F := closedLayer T A Λ ℓ N D i →ᵇ ℂ))
    (hcompare : ∀ i, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ (sf : HasStrongFellerKernel (C ε)) (f : closedLayer T A Λ ℓ N D i →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
      (R • transferOperator (𝕜 := ℂ) (chain (C ε) (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))
        (strongFeller (C ε) sf (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))) f = z • f →
      (models i).inputs.principal < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • (models i).inputs.operator ε))
    (σ : Measure X) (density : NNReal → X × X → ENNReal)
    (hdensity : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ x, (C ε).killedTransition x = σ.withDensity (fun y => density ε (x, y)))
    (hpre : ∀ B : Set X, σ B = 0 → σ (T ⁻¹' B) = 0)
    (hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0)
    (wc : closedLayer T A Λ ℓ N D j → ℝ) (hwc : Measurable wc)
    (hwcR : ∀ x, wc x ≤ R)
    (TestObservables : Set (closedLayer T A Λ ℓ N D j →ᵇ ℝ))
    (multipliers : TestObservables → E j →L[ℂ] E j)
    (sources : ∀ outputs : ProjectorOutputs (models j).inputs.operator
        (LeanShared.TwoNormNormalization.weakEmbedding (iW j)) det cutoff margin,
      ∀ η : ℝ, 0 < η → ∀ᶠ ε : NNReal in 𝓝[>] 0,
        Nonempty (NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
          T V (closedLayer T A Λ ℓ N D j) G
          (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
          (ρ ε) (F ε) (hF ε) (fun x => w x.val) hwK wc hwc R hR
          (fun x => hwR x.val) hwcR outputs ε η TestObservables multipliers)) :
    ∃ outputs : ProjectorOutputs (models j).inputs.operator
      (LeanShared.TwoNormNormalization.weakEmbedding (iW j)) det cutoff margin,
      ∀ᶠ ε : NNReal in 𝓝[>] 0, ∃ sf : HasStrongFellerKernel (C ε),
        let P := levels T A Λ ℓ N D k
        letI : CompactSpace P := isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D k (by omega) hkℓ)
        let CP := chain (C ε) P (ambient_levels_measurable T A hA Λ ℓ N D k)
        let sfP := strongFeller (C ε) sf P (ambient_levels_measurable T A hA Λ ℓ N D k)
        ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) CP sfP) (1 : P →ᵇ ℝ),
          (C ε).IsQuasiErgodic ((productMeasure CP sfP dg).map Subtype.val) ∧
          Λ (D.index j) ⊆ ((productMeasure CP sfP dg).map Subtype.val).support ∧
          (∀ x : P, x.val ∈ Λ (D.index j) → 0 < dg.eigenvector x) ∧
          ∃ dc : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
            (chain (C ε) (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j))
            (strongFeller (C ε) sf (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j)))
            (1 : closedLayer T A Λ ℓ N D j →ᵇ ℝ),
            dc.rate = R * (outputs.eigenvalue ε).re ∧
            ∃ μ : Measure (closedLayer T A Λ ℓ N D j), IsFiniteMeasure μ ∧
              (∀ f, dc.mean f = ∫ y, f y ∂μ) ∧
              (productMeasure CP sfP dg).map Subtype.val = (eigenvectorMeasure μ dc.eigenvector).map Subtype.val := by
  classical
  subst R
  let K := closedLayer T A Λ ℓ N D j
  have hK : IsCompact K := isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have hcoreEq : isolatedCore T K = Λ (D.index j) := closed_layer_core T A Λ ℓ N D hA j
  have hKLive : K ⊆ Aᶜ := by
    apply closure_minimal _ hA.isClosed_compl
    intro x hx hxA
    exact hx.2 (levels_monotone T A Λ ℓ N D (Nat.zero_le j.val)
      ((levels_zero T A Λ ℓ N D).symm ▸ hxA))
  let outputs := Classical.choice ((models j).inputs.exists_projector_outputs
    (essential j) kl (models j).injectiveW (models j).compactW det cutoff margin
    hαq hqr hqweak hsubq hmargin hmarginSub hmarginLead)
  obtain ⟨η, hη, hproduce⟩ :=
    ActualProducedClosedLayerSource.exists_uniform_noise_tolerance_for_actual_closed_layer_source
      (E := E j) (Weak := Weak j) (Z := Zret) (Ω := Ω)
      T Aᶜ V K G U hA.measurableSet.compl hKLive hV hVK hK hU
      (hcoreEq.symm ▸ hcoreU) hUV hUG hsep (hcoreEq.symm ▸ hcoreG)
      (hcoreEq.symm ▸ htrans) (hcoreEq.symm ▸ hΛ j) w hw hwK hwG (scale j) hR hwR
  refine ⟨outputs, ?_⟩
  let J : Finset (Fin ℓ) := Finset.univ.filter (fun i => i.val < k ∧ i ≠ j)
  obtain ⟨β, hβ, hbounds⟩ :=
    EventualDominantPressureGrowth.eventually_stratum_bounds_from_actual_projector_rate
      T A Λ ℓ N D hA hΛ E Mid Weak J pressure (pressure (D.index j))
      (fun i hi => hgap i (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hi).2.2)
      iH iW law prob generator scale models essential (fun i _ => confine i)
      (fun i _ => hdet i) (fun i _ => hprincipal i) j det cutoff margin outputs hpressure
      C hSF (fun _ => scale j) (fun i _ => hUltra i) (fun i _ => hFredholm i)
      (fun i _ => hcompare i)
      σ density hdensity hpre hnull
  filter_upwards [hbounds, sources outputs η hη, hnoUp, hSF,
    hactual, hzeroA, hdensity, self_mem_nhdsWithin]
    with ε hb hs hnoUpε sf hactualε hzeroAε hdensityε hε
  refine ⟨sf, ?_⟩
  let source := Classical.choice hs
  let : (ρ ε).IsOpenPosMeasure := hρ ε hε
  have hSFactual : HasStrongFellerKernel
      (NoiseKernel.chain (ρ ε) (F ε) (hF ε) Aᶜ hA.measurableSet.compl w hw (scale j) hR hwR) := by
    rw [← hactualε]
    exact sf
  let inputs := source.sameCutoff.originalInputs outputs hmarginSub hmarginLead hq ε
    _ _ source.cutoffSF source.originalSF (scale j) hR
  have hp := hproduce (ρ ε) (F ε) (hF ε) source.close source.plaques hSFactual inputs source.inverse
  have hop : (scale j • transferOperator (𝕜 := ℝ)
      (chain (C ε) K hK.measurableSet) (strongFeller (C ε) sf K hK.measurableSet)) =
      (scale j • transferOperator (𝕜 := ℝ)
        (chain (NoiseKernel.chain (ρ ε) (F ε) (hF ε) Aᶜ hA.measurableSet.compl w hw (scale j) hR hwR)
          K hK.measurableSet) (strongFeller _ hSFactual K hK.measurableSet)) := by
    simp only [hactualε]
  rw [← hop] at hp
  obtain ⟨dc, hrate, _hone, μ, hμ, hm, _hloc, hpos, hsupp⟩ := hp
  change dc.rate = scale j * (outputs.eigenvalue ε).re at hrate
  let : IsFiniteMeasure μ := hμ
  have hβdc : β < dc.rate := by rw [hrate]; exact hb.2.1
  have hleaves : ∀ i : Fin ℓ, i.val < k → i ≠ j → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖(scale j • transferOperator (𝕜 := ℝ)
        (chain (C ε) (stratum T A Λ ℓ N D i) (stratum_measurable T A Λ ℓ N D hA i))
        (strongFeller (C ε) sf (stratum T A Λ ℓ N D i)
          (stratum_measurable T A Λ ℓ N D hA i)))^n‖ ≤ B * β^n := by
    intro i hi hij
    exact hb.2.2 sf i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hij⟩)
  obtain ⟨dg, _hgrate, hqem, hid, hsupport, _hunique, hpositive, _hlimits⟩ :=
    ActualSelectedPrefixQuasiErgodic.exists_actual_selected_prefix_QEM
      T A hA Λ ℓ N D k hkℓ j hjk (C ε) sf hzeroAε (hnoUpε hε)
      (scale j) hR dc hβ hβdc hleaves σ (density ε) hdensityε hpre hnull μ hm (hΛ j)
      (fun x hx => hpos x (hcoreEq.symm ▸ hx)) (hcoreEq ▸ hsupp)
  exact ⟨dg, hqem, hsupport, hpositive, dc, hrate, μ, hμ, hm, hid⟩

end ConditionedStochasticStabilityHyperbolic.Global.EventualScaleSelectedPrefix
