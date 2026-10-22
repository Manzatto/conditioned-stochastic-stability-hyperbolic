module

public import ConditionedStochasticStabilityHyperbolic.Global.EventualScalePrefixSources
public import ConditionedStochasticStabilityHyperbolic.Global.ActualAbsorbingKernelSupport
public import ConditionedStochasticStabilityHyperbolic.Global.AssembleExactPrefixFamilies
public import ConditionedStochasticStabilityHyperbolic.Global.PaperLiveObservableLimits

/-! # All shifted actual model sources imply the conditional HG2 conclusions

Every prefix gap and physical product is produced inside this application.
The test duals may vary with the selected block and filtration shift, as the
actual supported collars and retained regular test spaces do.
The source record contains only constructed model data and exact ordinary
comparison/density/geometry facts. Local weak families and local uniqueness
are outputs of the checked local KL application. Neither At, Families nor a
global QEM/weak-limit conclusion is assumed. Strict trapping remains an
explicit geometric gate and is not attributed to literal HG2.
-/
public noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.EventualShiftedPrefixApplication
open AbsorbingMarkovChains LeanShared ShiftedFiltrationGeometry ActualFiltrationGrowth
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic DerivedHG2Application
open AssembleShiftedPrefixFamilies FiltrationPressureConfinement
variable {X I Ξ Ω : Type*}
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Ξ] [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))

variable (Z Zret Core : Fin t → ℕ → Type*)
  [∀ s N, NormedAddCommGroup (Core s N)] [∀ s N, NormedSpace ℂ (Core s N)]
  [∀ s N, NormedAddCommGroup (Z s N)] [∀ s N, NormedSpace ℂ (Z s N)]
  [∀ s N, NormedAddCommGroup (Zret s N)] [∀ s N, NormedSpace ℂ (Zret s N)]

local instance compactPrefix (s : Fin t) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D ((terminal s).val + 1) (by omega) (by have _h := (terminal s).isLt; omega))

include sf in
omit [CompactSpace X] [BorelSpace X] [SecondCountableTopology X] in
/-- The global positive-SF family may be the legitimate min-scale
continuation. Every physical source is required only on the original germ. -/
theorem eventualSF : ∀ᶠ ε : NNReal in 𝓝[>] 0, HasStrongFellerKernel (C ε) := by
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact sf ε hε

theorem conditional_global_global_from_eventual_scale_sources
    (sources : ∀ s N, EventualScalePrefixSources.Sources (Ξ := Ξ) (Ω := Ω) (Z := Z s N) (Zret := Zret s N) (Core := Core s N)
      T A hA Λ ℓ N D ((terminal s).val + 1) (by have _h := (terminal s).isLt; omega)
      (selectedIndex ℓ t terminal root s) (root s).isLt C (eventualSF C sf))
    (localFamily : ∀ s : Fin t, NNReal → ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)))
    (localUnique : ∀ s, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ ν : Measure (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)),
        (chain (C ε) (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))
          (closedLayer_measurable T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))).IsQuasiErgodic ν →
        {x | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))} ⊆ ν.support →
        ν = (localFamily s ε : Measure _))
    (equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ))
    (localWeak : ∀ s, Tendsto (fun ε => ProbabilityMeasure.map (localFamily s ε) Subtype.val)
      (𝓝[>] 0) (𝓝 (ProbabilityMeasure.map (equilibrium s) (Subtype.val : ↥(Aᶜ) → X))))
    (horder : ∀ s q : Fin t, s < q → (terminal q).val + 1 ≤ (root s).val)
    (geometry : DerivedHG2Basins.GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)
    (hℓ : 0 < ℓ) (c : ℝ) (hc : 0 ≤ c)
    (hnoise : ∀ ε : NNReal, 0 < ε → ∀ z ω,
      dist (geometry.maps ε (z, ω)) (T z) ≤ c * (ε : ℝ)) :
    ∃ family : Families T A hA Λ ℓ D t terminal root C sf,
      family.closedProduct = (fun s ε => (localFamily s ε : Measure _)) ∧
      family.equilibrium = equilibrium ∧
      ∃ δ : NNReal, 0 < δ ∧
        DerivedHG2Conclusions.ConclusionClauses T A hA Λ ℓ D t terminal root C sf family geometry δ := by
  let closedProduct (s : Fin t) (ε : NNReal) : Measure (closedLayer T A Λ ℓ 0 D
      (selectedIndex ℓ t terminal root s)) := localFamily s ε
  have hAt : ∀ s N, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε) := by
    intro s N
    obtain ⟨outputs, hproduce⟩ := (sources s N).produce
    filter_upwards [hproduce, (sources s N).hnoUp, localUnique s] with ε hp hn hu
    intro hε
    obtain ⟨sfε, dg, _hq, hsupp, hpos, dc, _hrate, μ, hμ, hm, hproduct⟩ := hp
    have hsfeq : sfε = sf ε hε := Subsingleton.elim _ _
    subst sfε
    let : IsFiniteMeasure μ := hμ
    apply at_of_actual_produced_pair T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε
      dg (hn hε ((terminal s).val + 1) le_rfl) hpos hsupp
      (sources s N).R (sources s N).hR dc μ hm hproduct
    intro hN
    subst N
    intro ν hν hs
    rw [hu hε ν hν hs]
  have hzero : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x A = 0 := by
    intro ε _hε x
    let : IsProbabilityMeasure (geometry.noise ε) := geometry.probability ε
    rw [geometry.actual_model ε]
    exact ActualAbsorbingKernelSupport.target_absorbing_mass_zero (geometry.noise ε)
      (geometry.maps ε) (geometry.measurable ε) A hA.measurableSet
      (fun x => Real.exp (geometry.potential x))
      (Real.measurable_exp.comp geometry.potential_measurable)
      geometry.R geometry.R_positive geometry.weight_bound x
  have hcore : ∀ s, (Λ (D.index (selectedIndex ℓ t terminal root s))).Nonempty :=
    fun s => (sources s 0).hΛ _
  have hprob : ∀ s ε, IsProbabilityMeasure (closedProduct s ε) := fun _ _ => inferInstance
  have hweak : ∀ s, Tendsto
      (fun ε => ProbabilityMeasure.map
        (⟨closedProduct s ε, hprob s ε⟩ : ProbabilityMeasure
          (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))) Subtype.val)
      (𝓝[>] 0) (𝓝 (ProbabilityMeasure.map (equilibrium s) (Subtype.val : ↥(Aᶜ) → X))) := by
    intro s
    have hpack : (fun ε => ProbabilityMeasure.map
        (⟨closedProduct s ε, hprob s ε⟩ : ProbabilityMeasure
          (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))) Subtype.val) =
        (fun ε => ProbabilityMeasure.map (localFamily s ε) Subtype.val) := by
      funext ε
      apply congrArg (fun ν : ProbabilityMeasure
        (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)) => ProbabilityMeasure.map ν Subtype.val)
      exact Subtype.ext rfl
    rw [hpack]
    exact localWeak s
  obtain ⟨family, hproducts, hequilibrium⟩ :=
    AssembleExactPrefixFamilies.families_of_produced_prefixes T A hA Λ ℓ D t terminal root C sf
      closedProduct hAt hzero hcore horder hprob equilibrium hweak
  obtain ⟨δ, hδ, hclauses⟩ := DerivedHG2Conclusions.conditional_global_global
    T A hA Λ ℓ D t terminal root C sf family geometry hℓ c hc hnoise
  exact ⟨family, hproducts, hequilibrium, δ, hδ, hclauses⟩

end ConditionedStochasticStabilityHyperbolic.Global.EventualShiftedPrefixApplication
