module

public import ConditionedStochasticStabilityHyperbolic.Global.EventualScaleSelectedPrefix
/-! # Explicit derived model sources for the actual global factory

Analytic projectors, the physical closed gap, pressure-slack growth of every
subordinate stratum, and the prefix gap/product are constructed in order.
This is a DERIVED interface: its physicalSources field is produced by the
actual ordinary-source manifold factory, and is not a cited classical input.
Only ordinary comparison/density/plaque sources remain at the analytic gate;
no physical gap, growth bound, prefix QEM or noisy rate convergence is input.
-/
public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
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

structure Sources (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hkℓ : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
    (hSF : ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε)) where
  hΛ : ∀ i : Fin ℓ, (Λ (D.index i)).Nonempty
  E : Fin ℓ → Type*
  Mid : Fin ℓ → Type*
  Weak : Fin ℓ → Type*
  [instance1 : ∀ i, NormedAddCommGroup (E i)]
  [instance2 : ∀ i, NormedSpace ℂ (E i)]
  [instance3 : ∀ i, CompleteSpace (E i)]
  [instance4 : ∀ i, Nontrivial (E i)]
  [instance5 : ∀ i, NormedAddCommGroup (Mid i)]
  [instance6 : ∀ i, NormedSpace ℂ (Mid i)]
  [instance7 : ∀ i, NormedAddCommGroup (Weak i)]
  [instance8 : ∀ i, NormedSpace ℂ (Weak i)]
  [instance9 : ∀ i, CompleteSpace (Weak i)]
  pressure : I → ℝ
  hgap : ∀ i : Fin ℓ, i.val < k → i ≠ j → pressure (D.index i) < pressure (D.index j)
  iH : ∀ i, E i →L[ℂ] Mid i
  iW : ∀ i, E i →L[ℂ] Weak i
  law : NNReal → Measure Ξ
  prob : ∀ ε, IsProbabilityMeasure (law ε)
  generator : ∀ i, NNReal → Ξ → E i →L[ℂ] E i
  scale : Fin ℓ → ℝ
  models : ∀ i, ProducedAnnealedModel.Data (iH i) (iW i) law prob (generator i) (scale i)
  essential : ∀ i, EssentialRadiusContract (E := E i) (W := Weak i)
  kl : ClassicalContract (E := E j) (W := Weak j)
  confine : ∀ i, ClassicalConfinementContract (E := E i) (W := Weak i)
  hdet : ∀ i, spectralRadius ℂ ((scale i : ℂ) • (models i).inputs.operator 0) ≤ ENNReal.ofReal (Real.exp (pressure (D.index i)))
  hprincipal : ∀ i, (models i).inputs.principal ≤ Real.exp (pressure (D.index i))
  det : DeterministicLeading ((models j).inputs.operator 0)
  cutoff : ℝ
  margin : ℝ
  hαq : (models j).inputs.principal / scale j < cutoff
  hqr : cutoff < det.rate
  hqweak : cutoff < (models j).inputs.weakRate / scale j
  hsubq : det.subordinate < cutoff
  hmargin : 0 < margin
  hmarginSub : margin < cutoff - det.subordinate
  hmarginLead : margin < det.rate - cutoff
  hq : 0 < cutoff
  hpressure : scale j * det.rate = Real.exp (pressure (D.index j))
  R : ℝ
  hR : 0 < R
  hscaleJ : scale j = R
  V : Set X
  G : Set X
  U : Set X
  hV : IsOpen V
  hVK : V ⊆ closedLayer T A Λ ℓ N D j
  hU : IsOpen U
  hcoreU : Λ (D.index j) ⊆ U
  hUV : closure U ⊆ V
  hUG : closure U ⊆ G
  hsep : (T '' closure U) ∩ forwardTrapped T (closedLayer T A Λ ℓ N D j) ⊆ U
  hcoreG : Λ (D.index j) ⊆ G
  htrans : forwardTransitiveOn T (Λ (D.index j))
  w : X → ℝ
  hw : Measurable w
  hwK : Continuous (fun x : closedLayer T A Λ ℓ N D j => w x.val)
  hwG : ∀ x : closedLayer T A Λ ℓ N D j, x.val ∈ G → 0 < w x.val
  hwR : ∀ x, w x ≤ R
  ρ : NNReal → Measure Ω
  [instance10 : ∀ ε, IsProbabilityMeasure (ρ ε)]
  hρ : ∀ ε, 0 < ε → (ρ ε).IsOpenPosMeasure
  F : NNReal → X × Ω → X
  hF : ∀ ε, Measurable (F ε)
  hactual : ∀ᶠ ε : NNReal in 𝓝[>] 0, C ε = NoiseKernel.chain (ρ ε) (F ε) (hF ε) Aᶜ hA.measurableSet.compl w hw R hR hwR
  hnoUp : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε, ∀ i, i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
      (C ε).killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0
  hzeroA : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ x, (C ε).killedTransition x A = 0
  hUltra : ∀ i, StrongFellerSquareCompact.UltraFellerContract (X := closedLayer T A Λ ℓ N D i)
  hFredholm : ∀ i, PowerCompactGap.SquareCompactFredholm (F := closedLayer T A Λ ℓ N D i →ᵇ ℂ)
  hcompare : ∀ i, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ (sf : HasStrongFellerKernel (C ε)) (f : closedLayer T A Λ ℓ N D i →ᵇ ℂ), f ≠ 0 → ∀ z : ℂ,
      (R • transferOperator (𝕜 := ℂ) (chain (C ε) (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))
        (strongFeller (C ε) sf (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i))) f = z • f →
      (models i).inputs.principal < ‖z‖ → z ∈ spectrum ℂ ((scale i : ℂ) • (models i).inputs.operator ε)
  σ : Measure X
  density : NNReal → X × X → ENNReal
  hdensity : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ x, (C ε).killedTransition x = σ.withDensity (fun y => density ε (x, y))
  hpre : ∀ B : Set X, σ B = 0 → σ (T ⁻¹' B) = 0
  hnull : ∀ i, 0 < i → i ≤ ℓ → σ (frontier (D.levels i)) = 0
  cutoffWeight : closedLayer T A Λ ℓ N D j → ℝ
  cutoff_measurable : Measurable cutoffWeight
  cutoff_bound : ∀ x, cutoffWeight x ≤ R
  tests : Set (closedLayer T A Λ ℓ N D j →ᵇ ℝ)
  multipliers : tests → E j →L[ℂ] E j
  physicalSources : ∀ outputs : ProjectorOutputs (models j).inputs.operator
      (LeanShared.TwoNormNormalization.weakEmbedding (iW j)) det cutoff margin,
    ∀ η : ℝ, 0 < η → ∀ᶠ ε : NNReal in 𝓝[>] 0,
      Nonempty (NoFullSupportKLFamily.ScaleSources (Z := Z) (Zret := Zret) (Core := Core)
        T V (closedLayer T A Λ ℓ N D j) G
        (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
        (ρ ε) (F ε) (hF ε) (fun x => w x.val) hwK cutoffWeight cutoff_measurable R hR
        (fun x => hwR x.val) cutoff_bound outputs ε η tests multipliers)


attribute [instance] Sources.instance1 Sources.instance2 Sources.instance3 Sources.instance4 Sources.instance5 Sources.instance6 Sources.instance7 Sources.instance8 Sources.instance9 Sources.instance10

variable (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (k : ℕ) (hkℓ : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
    (hSF : ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε))

theorem Sources.produce (s : Sources (Ξ := Ξ) (Ω := Ω) (Z := Z) (Zret := Zret) (Core := Core) T A hA Λ ℓ N D k hkℓ j hjk C hSF) :
    ∃ outputs : ProjectorOutputs (s.models j).inputs.operator
      (LeanShared.TwoNormNormalization.weakEmbedding (s.iW j)) s.det s.cutoff s.margin,
      ∀ᶠ ε : NNReal in 𝓝[>] 0, ∃ sf : HasStrongFellerKernel (C ε),
        let P := levels T A Λ ℓ N D k
        letI : CompactSpace P := isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D k (by have _h := hjk; omega) hkℓ)
        let CP := chain (C ε) P (ambient_levels_measurable T A hA Λ ℓ N D k)
        let sfP := strongFeller (C ε) sf P (ambient_levels_measurable T A hA Λ ℓ N D k)
        ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) CP sfP) (1 : P →ᵇ ℝ),
          (C ε).IsQuasiErgodic ((productMeasure CP sfP dg).map Subtype.val) ∧
          Λ (D.index j) ⊆ ((productMeasure CP sfP dg).map Subtype.val).support ∧
          (∀ x : P, x.val ∈ Λ (D.index j) → 0 < dg.eigenvector x) ∧
          ∃ dc : RankOneSpectralData (s.R • transferOperator (𝕜 := ℝ)
            (chain (C ε) (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j))
            (strongFeller (C ε) sf (closedLayer T A Λ ℓ N D j) (closedLayer_measurable T A Λ ℓ N D j)))
            (1 : closedLayer T A Λ ℓ N D j →ᵇ ℝ),
            dc.rate = s.R * (outputs.eigenvalue ε).re ∧
            ∃ μ : Measure (closedLayer T A Λ ℓ N D j), IsFiniteMeasure μ ∧
              (∀ f, dc.mean f = ∫ y, f y ∂μ) ∧
              (productMeasure CP sfP dg).map Subtype.val = (eigenvectorMeasure μ dc.eigenvector).map Subtype.val := by
  exact EventualScaleSelectedPrefix.exists_literal_global_package_from_produced_models
    (Z := Z) (Zret := Zret) (Core := Core) T A hA Λ ℓ N D k hkℓ j hjk
    s.hΛ s.E s.Mid s.Weak s.pressure s.hgap s.iH s.iW s.law s.prob s.generator s.scale
    s.models s.essential s.kl s.confine s.hdet s.hprincipal s.det s.cutoff s.margin
    s.hαq s.hqr s.hqweak s.hsubq s.hmargin s.hmarginSub s.hmarginLead s.hq s.hpressure
    s.R s.hR s.hscaleJ s.V s.G s.U s.hV s.hVK s.hU s.hcoreU s.hUV s.hUG s.hsep s.hcoreG
    s.htrans s.w s.hw s.hwK s.hwG s.hwR s.ρ s.hρ s.F s.hF C s.hactual hSF s.hnoUp s.hzeroA
    s.hUltra s.hFredholm s.hcompare s.σ s.density s.hdensity s.hpre s.hnull
    s.cutoffWeight s.cutoff_measurable s.cutoff_bound s.tests s.multipliers s.physicalSources

end ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
