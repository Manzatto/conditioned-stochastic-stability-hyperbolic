module
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationPrefixSources
public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies
meta import Lean.LibrarySuggestions.Basic

/-! Every shifted prefix of every selected block from native packets (global route, HG2). One
representation of the literal perturbation identifies the global chain with all prefix chains near
zero; the selected local families identify the base products by qualified uniqueness. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "NativeFiltrationShiftedPrefixes"

public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationShiftedPrefixes
open LeanShared LeanShared.HyperbolicBasicSet RegularNoise Global
open Global.ShiftedFiltrationGeometry Global.FiltrationPressureConfinement
open DerivedHG2Application AssembleShiftedPrefixFamilies

universe uι
variable {E : Type*} {ι : Type uι} {M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M] [Fintype ι]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

/-- Every shifted prefix of every selected block, natively. -/
theorem produce
    {T : M ≃ₜ M} {I : Type} (Λ : I → Set M) (g : M → ℝ) (A : Set M) (hA : IsOpen A)
    (strict : MapsTo T (closure A) A) {ℓ : ℕ} (D : AdaptedSource T A Λ ℓ)
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
    (t : ℕ) (terminal : Fin t → Fin ℓ) (root : ∀ s, Fin ((terminal s).val + 1))
    (mixing : ∀ s, HyperbolicBasicSet.MixingOn T
      (Λ (D.index (selectedIndex ℓ t terminal root s))))
    (equilibrium : ∀ s, EquilibriumPackage
      (basic (selectedIndex ℓ t terminal root s)).hyperbolic g)
    (pressure_gap : ∀ s (i : Fin ℓ), i.val < (terminal s).val + 1 →
      i ≠ selectedIndex ℓ t terminal root s →
      pressure (D.index i) < pressure (D.index (selectedIndex ℓ t terminal root s)))
    (shifted_boundary_null : ∀ n i, 0 < i → i ≤ ℓ →
      σ (frontier (levels T A Λ ℓ n D i)) = 0)
    (C : ℝ≥0 → AbsorbingMarkovChains.CanonicalChain M)
    (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
    (same : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, C ε =
      NoiseKernel.chain (L.fixedLaw ε)
        (fun z : M × RegularNoise.FixedControl (ι := ι) => evaluate (p.fixedParameters ε z.2) z.1)
        (p.allScale_measurable ε) Aᶜ hA.measurableSet.compl w hw.measurable R
        (zero_lt_one.trans_le hR1) hwR)
    (localFamily : ∀ s : Fin t, ℝ≥0 → ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)))
    (localUnique : ∀ s, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ ν : Measure (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)),
        (RestrictedLayerChain.chain (C ε)
          (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))
          (closedLayer_measurable T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))).IsQuasiErgodic ν →
        {x | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))} ⊆ ν.support →
        ν = (localFamily s ε : Measure _)) :
    ∀ s N, ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf
        (fun s ε => (localFamily s ε : Measure _)) s N ε hε) := by
  intro s N
  let prepared := NativeFiltrationPrefixSources.prefixSources Λ g A hA strict N D basic live r1 regularT
    inverseRegular w hw wPos coreWeight localWeight stable pressure pressure_identity P L R hR1 hRP
    hwR p σ source source.smooth_density ((terminal s).val + 1)
    (by have h := (terminal s).isLt; omega) (selectedIndex ℓ t terminal root s) (root s).isLt
    (mixing s) (equilibrium s) (pressure_gap s) shifted_boundary_null C same
  obtain ⟨outputs, hproduce⟩ := prepared.sources.produce
  filter_upwards [hproduce, prepared.sources.hnoUp, localUnique s] with ε hp hn hu
  intro hε
  obtain ⟨sfε, dg, _hq, hsupp, hpos, dc, _hrate, μ, hμ, hm, hproduct⟩ := hp
  have hsfeq : sfε = sf ε hε := Subsingleton.elim _ _
  subst sfε
  let : IsFiniteMeasure μ := hμ
  apply at_of_actual_produced_pair T A hA Λ ℓ D t terminal root C sf
    (fun s ε => (localFamily s ε : Measure _)) s N ε hε
    dg (hn hε ((terminal s).val + 1) le_rfl) hpos hsupp prepared.sources.R prepared.sources.hR dc μ hm hproduct
  intro hN
  subst N
  intro ν hν hs
  rw [hu hε ν hν hs]

end ConditionedStochasticStabilityHyperbolic.Paper.NativeFiltrationShiftedPrefixes
