module

public import ConditionedStochasticStabilityHyperbolic.Global.BoundaryNullDensityReference

public import ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalAnalyticArrayData
import all ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalPrefixSources
public import ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerSelectedPacket
public import ConditionedStochasticStabilityHyperbolic.Paper.ClosedLayerPacketArray

public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory ProbabilityTheory IsManifold
open scoped Topology NNReal Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalNullPacketApplication
open LeanShared Global ShiftedFiltrationGeometry ActualFiltrationGrowth
open PhysicalClassicalLayer KellerLiverani1999 ComplexStrongFeller RestrictedLayerChain
open FiltrationPressureConfinement DyadicCompletion SmoothSupportedManifoldCore
open PhysicalClassicalPrefixSources LeanShared.ControlledPlaqueClosure
universe uM uE

local instance compactLayer {M I : Type*} [MetricSpace M] [CompactSpace M]
    (T : M ≃ₜ M) (A : Set M) (Λ : I → Set M) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (i : Fin ℓ) : CompactSpace (closedLayer T A Λ ℓ N D i) :=
  isCompact_iff_compactSpace.mp (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))

structure Geometry {M I : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M]
    (T : M ≃ₜ M) (A : Set M) (Λ : I → Set M) (ℓ N : ℕ)
    (D : AdaptedSource T A Λ ℓ) (w : M → ℝ) (pressure : I → ℝ)
    (k : ℕ) (j : Fin ℓ) (G B : Set M) (σ : Measure M) where
  nonempty_basic : ∀ i : Fin ℓ, (Λ (D.index i)).Nonempty
  pressure_gap : ∀ i : Fin ℓ, i.val < k → i ≠ j → pressure (D.index i) < pressure (D.index j)
  strict_trapping : MapsTo T (closure A) A
  shifted_boundary_null : ∀ n i, 0 < i → i ≤ ℓ →
    σ (frontier (levels T A Λ ℓ n D i)) = 0
  retained_collar : closure B ⊆ G
  weight_collar : ∀ x : closedLayer T A Λ ℓ N D j, x.val ∈ G → 0 < w x.val
  transitive : forwardTransitiveOn T (Λ (D.index j))

def assembledPacketSources
{M : Type uM} {E : Type uE}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  {ι I : Type*} [Fintype ι] {T : M ≃ₜ M} {r : ℝ}
  (F : RegularNoise.Maps (E := E) (ι := ι) T r)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (A : Set M) (hA : IsOpen A) (Λ : I → Set M) (ℓ N : ℕ)
  (D : AdaptedSource T A Λ ℓ) (w : M → ℝ) (R : ℝ) (pressure : I → ℝ)



(frames : ∀ i : Fin ℓ,
  Frame F σ (closedLayer T A Λ ℓ N D i) (layerCompact A Λ ℓ N D i) w R (pressure (D.index i)))



    (L : RegularNoise.Laws (ι := ι)) (k : ℕ) (hk : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (hw : Continuous w) (hnonnegative : ∀ x, 0 ≤ w x) (hR : 0 < R) (bound : ∀ x, w x ≤ R)
    (geometry : Geometry T A Λ ℓ N D w pressure k j (frames j).G (frames j).B σ)
    (packets : ∀ i : Fin ℓ, ClosedLayerAnalyticPacket.Data (closedLayer T A Λ ℓ N D i)
      (fun ε => RestrictedNoise.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) =>
          (frames i).model.maps ((frames i).representation.fixedParameters ε z.2) z.1)
        ((frames i).representation.allScale_measurable ε)
        (closedLayer T A Λ ℓ N D i) (closedLayer_measurable T A Λ ℓ N D i)
        (fun x => w x.val) (hw.measurable.comp measurable_subtype_coe) R hR (fun x => bound x.val))
      L.fixedLaw (fun _ => inferInstance) R (pressure (D.index i)))
    (selection : ClosedLayerAnalyticPacket.Selection (packets j) T (frames j).V (frames j).G
      (layerCompact A Λ ℓ N D j) L.fixedLaw
      (fun ε (z : M × RegularNoise.FixedControl (ι := ι)) =>
        (frames j).model.maps ((frames j).representation.fixedParameters ε z.2) z.1)
      (frames j).representation.allScale_measurable (fun x => w x.val) (frames j).cutoff
      (frames j).source.weight_continuous (frames j).source.cutoff_measurable hR
      (fun x => bound x.val) (frames j).source.cutoff_bound)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain M)
    (same : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, C ε =
      actualChain F σ A hA Λ ℓ N D w R pressure frames L j hw hR bound ε) :
    Σ' sf : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel (C ε),
      EventualScalePrefixSources.Sources (Ξ := RegularNoise.FixedControl (ι := ι))
        (Ω := RegularNoise.FixedControl (ι := ι)) (Z := selection.Z) (Zret := selection.Zret)
        (Core := selection.Core) T A hA Λ ℓ N D k hk j hjk C sf := by
  letI : ∀ i, NormedAddCommGroup (packets i).Strong := fun i => (packets i).strongNormed
  letI : ∀ i, NormedSpace ℂ (packets i).Strong := fun i => (packets i).strongScalar
  letI : ∀ i, CompleteSpace (packets i).Strong := fun i => (packets i).strongComplete
  letI : ∀ i, Nontrivial (packets i).Strong := fun i => (packets i).strongNontrivial
  letI : ∀ i, NormedAddCommGroup (packets i).Weak := fun i => (packets i).weakNormed
  letI : ∀ i, NormedSpace ℂ (packets i).Weak := fun i => (packets i).weakScalar
  letI : ∀ i, CompleteSpace (packets i).Weak := fun i => (packets i).weakComplete
  have hSF : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, HasStrongFellerKernel (C ε) := by
    filter_upwards [same, eventually_strongFeller F σ A hA Λ ℓ N D w R pressure frames
      L j hw hnonnegative hR bound (frames j).source.submersion.smooth_density] with ε he hs
    simpa only [he] using hs
  have noUp : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ i, i ≤ k → ∀ x ∈ levels T A Λ ℓ N D i,
        (C ε).killedTransition x (levels T A Λ ℓ N D i)ᶜ = 0 := by
    filter_upwards [same, eventually_noUp F σ A hA Λ ℓ N D w R pressure frames
      L j hw hR bound geometry.strict_trapping] with ε he hn
    intro _hε i hi x hx
    rw [he]
    exact hn i (hi.trans hk) x hx
  have zeroA : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x, (C ε).killedTransition x A = 0 := by
    filter_upwards [same] with ε he
    intro x
    rw [he]
    exact ActualAbsorbingKernelSupport.target_absorbing_mass_zero (L.fixedLaw ε)
      (fun z : M × RegularNoise.FixedControl (ι := ι) =>
        (frames j).model.maps ((frames j).representation.fixedParameters ε z.2) z.1)
      ((frames j).representation.allScale_measurable ε) A hA.measurableSet w hw.measurable R hR bound x
  let densityExistence := exists_actual_density F σ A hA Λ ℓ N D w R pressure frames L j hw hR bound
  let density := Classical.choose densityExistence
  have hdensity : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ x,
      (C ε).killedTransition x = σ.withDensity (fun y => density ε (x, y)) := by
    filter_upwards [same, (Classical.choose_spec densityExistence).2] with ε he hd
    simpa only [he] using hd
  have hcore := closed_layer_core T A Λ ℓ N D hA j
  let noise := (frames j).source.noise
  refine ⟨hSF, ?_⟩
  exact {
    hΛ := geometry.nonempty_basic
    E := fun i => (packets i).Strong
    Mid := fun i => (packets i).Weak
    Weak := fun i => (packets i).Weak
    pressure := pressure
    hgap := geometry.pressure_gap
    iH := fun i => (packets i).inclusion
    iW := fun i => (packets i).inclusion
    law := L.fixedLaw
    prob := fun _ => inferInstance
    generator := fun i => (packets i).generator
    scale := fun _ => R
    models := fun i => (packets i).model
    essential := fun i => (packets i).essential
    kl := selection.kl
    confine := fun i => (packets i).confinement
    hdet := fun i => (packets i).reference_radius.le
    hprincipal := fun i => (packets i).principal_below_pressure.le
    det := selection.det
    cutoff := selection.cutoff
    margin := selection.margin
    hαq := selection.principal_lt
    hqr := selection.cutoff_lt_rate
    hqweak := selection.cutoff_lt_weak
    hsubq := selection.subordinate_lt
    hmargin := selection.margin_positive
    hmarginSub := selection.margin_subordinate
    hmarginLead := selection.margin_leading
    hq := selection.cutoff_positive
    hpressure := selection.rate_pressure
    R := R
    hR := hR
    hscaleJ := rfl
    V := (frames j).V
    G := (frames j).G
    U := (frames j).B
    hV := noise.live_open
    hVK := noise.live_subset
    hU := noise.retained_open
    hcoreU := hcore ▸ noise.core_retained
    hUV := noise.retained_live
    hUG := geometry.retained_collar
    hsep := noise.no_return
    hcoreG := hcore ▸ noise.core_collar
    htrans := geometry.transitive
    w := w
    hw := hw.measurable
    hwK := (frames j).source.weight_continuous
    hwG := geometry.weight_collar
    hwR := bound
    ρ := L.fixedLaw
    hρ := L.fixedLaw_full_support
    F := fun ε (z : M × RegularNoise.FixedControl (ι := ι)) =>
      (frames j).model.maps ((frames j).representation.fixedParameters ε z.2) z.1
    hF := (frames j).representation.allScale_measurable
    hactual := same
    hnoUp := noUp
    hzeroA := zeroA
    hUltra := fun i => (frames i).source.noise.ultra
    hFredholm := fun i => (frames i).source.noise.fredholm
    hcompare := ClosedLayerAnalyticPacket.spectralComparisons L.fixedLaw
      (fun i ε (z : M × RegularNoise.FixedControl (ι := ι)) =>
        (frames i).model.maps ((frames i).representation.fixedParameters ε z.2) z.1)
      (fun i => (frames i).representation.allScale_measurable)
      Aᶜ hA.measurableSet.compl (fun i => closedLayer T A Λ ℓ N D i)
      (fun i => closedLayer_measurable T A Λ ℓ N D i)
      (LiveFiltrationRealization.closed_layer_subset_live T A Λ ℓ N D hA)
      w hw.measurable R hR bound (fun _ => R) (fun i => pressure (D.index i))
      (fun _ => hR) (fun _ => bound) L.fixedLaw (fun _ => inferInstance) packets C
      (fun i => by
        filter_upwards [same, eventually_actual_each F σ A hA Λ ℓ N D w R pressure frames L j i hw hR bound]
          with ε hs hi
        exact hs.trans hi)
    σ := ForwardNullReference.reference T σ
    density := fun ε z => ((C ε).killedTransition z.1).rnDeriv
      (ForwardNullReference.reference T σ) z.2
    hdensity := BoundaryNullDensityReference.eventually_density T σ C density hdensity
    hpre := ForwardNullReference.preimage_null T T.measurableEmbedding σ
    hnull := BoundaryNullDensityReference.positive_boundary T A Λ ℓ D σ
      geometry.shifted_boundary_null
    cutoffWeight := (frames j).cutoff
    cutoff_measurable := (frames j).source.cutoff_measurable
    cutoff_bound := (frames j).source.cutoff_bound
    tests := selection.tests
    multipliers := selection.multipliers
    physicalSources := selection.physicalSources }

end ConditionedStochasticStabilityHyperbolic.Paper.PhysicalClassicalNullPacketApplication
