module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationLayers
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeNullPrefixSources
public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedMapAgreement
public import ConditionedStochasticStabilityHyperbolic.Paper.CompactClassicalPrefixSourcesData
meta import Lean.LibrarySuggestions.Basic

/-! The eventual prefix sources of an adapted filtration from native packets. Every closed layer
receives its native packet; the selected layer is replaced by the packet of its native
selection, whose carrier collars give the retained geometry. The noisy maps are those of one
representation of the literal perturbation. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeFiltrationPrefixSources"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationPrefixSources
open LeanShared LeanShared.HyperbolicBasicSet RegularNoise Global
open Global.ShiftedFiltrationGeometry Global.FiltrationPressureConfinement

universe uι
variable {E : Type*} {ι : Type uι} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- The native eventual prefix sources. -/
def prefixSources
    {T : M ≃ₜ M} {I : Type} (Λ : I → Set M) (g : M → ℝ) (A : Set M) (hA : IsOpen A)
    (strict : MapsTo T (closure A) A) {ℓ : ℕ} (N : ℕ) (D : AdaptedSource T A Λ ℓ)
    {Vb : Fin ℓ → Set M} (basic : ∀ i : Fin ℓ, BasicData (E := E) T (Λ (D.index i)) (Vb i))
    (live : ∀ i : Fin ℓ, Λ (D.index i) ⊆ Aᶜ)
    {r : ℝ} (r1 : 1 < r)
    (regularT : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (w : M → ℝ) (hw : Continuous w) (wPos : ∀ x, 0 < w x)
    (coreWeight : ∀ i : Fin ℓ, EqOn g w (Λ (D.index i)))
    (localWeight : ∀ i : Fin ℓ, ∃ W : Set M, IsOpen W ∧ Λ (D.index i) ⊆ W ∧
      ∀ ζ : M → ℝ, ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ)) ∞ ζ → tsupport ζ ⊆ W →
        FractionalManifoldRegularity.Regular (E := E) (F := ℝ) (r - 1) (ζ * w))
    (stable : ∀ i : Fin ℓ, ∀ x ∈ Λ (D.index i),
      0 < Module.finrank ℝ ((basic i).hyperbolic.stable x))
    (pressure : I → ℝ)
    (pressure_identity : ∀ i : Fin ℓ, ThermodynamicDefinitions.pressure T ((basic i).hyperbolic.potential g)
      (Λ (D.index i)) = (pressure (D.index i) : EReal))
    (P : RegularNoise.Maps (E := E) (ι := ι) T r) (L : RegularNoise.Laws (ι := ι))
    (R : ℝ) (hR1 : 1 ≤ R) (hRP : ∀ i : Fin ℓ, Real.exp (pressure (D.index i)) + 1 ≤ R)
    (hwR : ∀ x, w x ≤ R)
    {Parameters : Type*} [MetricSpace Parameters] {evaluate : Parameters → M → M}
    (p : RegularNoise.Representation P Parameters evaluate)
    (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
    (source : RegularNoise.ControlSubmersionSources (E := E) (ι := ι) σ)
    (smooth : RegularNoise.SmoothCubeSubmersionContract (E := E) (M := M) (ι := ι))
    (k : ℕ) (hk : k ≤ ℓ) (j : Fin ℓ) (hjk : j.val < k)
    (mixing : HyperbolicBasicSet.MixingOn T (Λ (D.index j)))
    (equilibrium : EquilibriumPackage (basic j).hyperbolic g)
    (pressure_gap : ∀ i : Fin ℓ, i.val < k → i ≠ j →
      pressure (D.index i) < pressure (D.index j))
    (shifted_boundary_null : ∀ n i, 0 < i → i ≤ ℓ →
      σ (frontier (levels T A Λ ℓ n D i)) = 0)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain M)
    (same : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, C ε =
      NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Aᶜ hA.measurableSet.compl w hw.measurable R
        (zero_lt_one.trans_le hR1) hwR) :
    CompactClassicalPrefixSources.Produced.{0, 0, uι, 0, 0, 0, 0, 0, 0} (ι := ι) T A hA Λ ℓ N D
      k hk j hjk C := by
  classical
  let Fg := fun ε (z : M × RegularNoise.FixedControl (ι := ι)) => evaluate (p.fixedParameters ε z.2) z.1
  let sel := Classical.choice (NativeFiltrationLayers.exists_selected Λ g A hA strict N D basic live
    r1 regularT inverseRegular w hw wPos coreWeight localWeight stable pressure
    pressure_identity P L R hR1 hRP hwR Fg p.allScale_measurable p.eventually_fixedMap j mixing
    equilibrium)
  let base := fun i : Fin ℓ => Classical.choice (NativeFiltrationLayers.exists_packet Λ g A hA
    strict N D basic live r1 regularT inverseRegular w hw wPos coreWeight localWeight stable pressure
    pressure_identity P L R hR1 hRP hwR Fg p.allScale_measurable p.eventually_fixedMap i)
  let packets := Function.update base j sel.packet
  let selection : NativeNullPrefixSources.NativeSelection.{0, 0, 0, _, _, _, 0, 0} (packets j) T sel.V sel.G
      (NativeNullPrefixSources.layerCompact T A Λ ℓ N D j) L.fixedLaw Fg p.allScale_measurable
      (fun x => w x.val) sel.cutoff (hw.comp continuous_subtype_val) sel.cutoff_measurable
      (zero_lt_one.trans_le hR1) (fun x => hwR x.val) sel.cutoff_bound := by
    simpa only [packets, Function.update_self] using sel.selection
  have geometry : PhysicalClassicalNullPacketApplication.Geometry T A Λ ℓ N D w pressure k j
      sel.G sel.B σ := {
    nonempty_basic := fun i => (basic i).nonempty
    pressure_gap := pressure_gap
    strict_trapping := strict
    shifted_boundary_null := shifted_boundary_null
    retained_collar := sel.retained_collar
    weight_collar := fun x _ => wPos x.val
    transitive := mixing.forwardTransitiveOn }
  let prepared := NativeNullPrefixSources.assembled P p σ source smooth A hA Λ ℓ N D w R pressure L k
    hk j hjk hw (fun x => (wPos x).le) (zero_lt_one.trans_le hR1) hwR sel.V sel.G sel.B geometry
    sel.live_open sel.live_subset sel.retained_open sel.core_retained sel.retained_live
    sel.no_return sel.core_collar sel.cutoff sel.cutoff_measurable sel.cutoff_bound packets
    selection C same
  exact {
    Z := selection.Z
    Zret := selection.Zret
    Core := selection.Core
    sf := prepared.1
    sources := prepared.2 }

end ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationPrefixSources
