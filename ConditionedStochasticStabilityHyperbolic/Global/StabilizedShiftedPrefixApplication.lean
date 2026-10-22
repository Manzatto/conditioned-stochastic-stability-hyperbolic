module

public import ConditionedStochasticStabilityHyperbolic.Global.RepresentedProductPrefixGap
public import ConditionedStochasticStabilityHyperbolic.Global.MarginalPrefixAssembly
public import ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.EventualShiftedPrefixApplication

/-! All HG2 clauses for the original system from the outputs of the ordinary
stabilized prefix and local-source factories. Original endpoint gaps and
product eigenmeasures are constructed internally; every prefix retains the
exact first marginal. Strict trapping remains in the explicit geometry. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.StabilizedShiftedPrefixApplication
open LeanShared Paper Paper.RegularNoise Paper.ActualProductRestrictedChain
open ComplexStrongFeller LayerQuasiErgodic ShiftedFiltrationGeometry ActualFiltrationGrowth
open DerivedHG2Application AssembleShiftedPrefixFamilies FiltrationPressureConfinement
variable {X Y E H I ι κ Ω : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [ChartedSpace E X] [ChartedSpace H Y]
  [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (S : Y ≃ₜ Y) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (G : Maps (E := H) (ι := κ) S r)
  (L : Laws (ι := ι)) (L' : Laws (ι := κ))
  (w : X → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R)
  (bound : ∀ x, w x ≤ R) (nonnegative : ∀ x, 0 ≤ w x)
  (C : NNReal → AbsorbingMarkovChains.CanonicalChain X)
  (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))
  (CP : NNReal → AbsorbingMarkovChains.CanonicalChain (X × Y))
  (sfP : ∀ ε, 0 < ε → HasStrongFellerKernel (CP ε))

local notation "DP" => ProductAdaptedFiltration.source T S A Λ ℓ D
set_option quotPrecheck false in
local notation "AP" => (A ×ˢ (univ : Set Y))
set_option quotPrecheck false in
local notation "LP" => (fun i => Λ i ×ˢ (univ : Set Y))
local notation "hAP" => hA.prod isOpen_univ
local instance prefixCompact (s : Fin t) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D
    ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega))
local instance productPrefixCompact (s : Fin t) (N : ℕ) :
    CompactSpace (actualPrefix (T.prodCongr S) AP LP ℓ DP (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact (T.prodCongr S) AP LP ℓ N DP
    ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega))
local instance auxCompact : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ

omit [SecondCountableTopology X] [CompactSpace Ω] in
include nonnegative sfP in
set_option maxHeartbeats 1600000 in
 theorem all_clauses_from_produced_prefixes
    (closedProduct : ∀ s, NNReal → Measure (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s)))
    (closedProductP : ∀ s, NNReal → Measure
      (closedLayer (T.prodCongr S) AP LP ℓ 0 DP (selectedIndex ℓ t terminal root s)))
    (produced : ∀ s N, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At (T.prodCongr S) AP hAP LP ℓ DP t terminal root CP sfP closedProductP s N ε hε))
    (actual : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ (hε : 0 < ε)
      (hwindow : ε ≤ min F.window G.window),
      C ε = NoiseKernel.chain (L.law ε) (actualMap F ε)
        (actualMap_measurable F ε hε (le_min_iff.mp hwindow).1) Aᶜ hA.measurableSet.compl
        w hw R hR bound ∧
      CP ε = NoiseKernel.chain ((productLaws L L').law ε)
        (joint ε (actualMap F ε) (actualMap G ε))
        (measurable_joint ε (actualMap F ε) (actualMap G ε)
          (actualMap_measurable F ε hε (le_min_iff.mp hwindow).1)
          (actualMap_measurable G ε hε (le_min_iff.mp hwindow).2))
        APᶜ (hAP).measurableSet.compl (fun z => w z.1) (hw.comp measurable_fst)
        R hR (fun z => bound z.1))
    (auxiliary : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ (hε : 0 < ε)
      (hwindow : ε ≤ min F.window G.window), ∃ νY : ProbabilityMeasure (univ : Set Y),
      LocalConclusions.NormalizedGap
        (ActualCompactNoiseGap.auxiliaryLocal F G L' ε hε hwindow 1 le_rfl) univ νY)
    (invariant : ∀ s N, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) N,
        (C ε).killedTransition x (actualPrefix T A Λ ℓ D (terminal s) N)ᶜ = 0)
    (core_live : ∀ s, Λ (D.index (selectedIndex ℓ t terminal root s)) ⊆ Aᶜ)
    (marginal : ∀ s ε, (closedProduct s ε).map Subtype.val =
      (closedProductP s ε).map (fun z => z.val.1))
    (hprob : ∀ s ε, IsProbabilityMeasure (closedProduct s ε))
    (equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ))
    (localWeak : ∀ s, Tendsto
      (fun ε => ProbabilityMeasure.map
        (⟨closedProduct s ε, hprob s ε⟩ : ProbabilityMeasure _) Subtype.val)
      (𝓝[>] 0) (𝓝 (ProbabilityMeasure.map (equilibrium s) (Subtype.val : ↥(Aᶜ) → X))))
    (hcore : ∀ s, (Λ (D.index (selectedIndex ℓ t terminal root s))).Nonempty)
    (horder : ∀ s q : Fin t, s < q → (terminal q).val + 1 ≤ (root s).val)
    (geometry : DerivedHG2Basins.GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)
    (hℓ : 0 < ℓ) (c : ℝ) (hc : 0 ≤ c)
    (hnoise : ∀ ε : NNReal, 0 < ε → ∀ z ω,
      dist (geometry.maps ε (z, ω)) (T z) ≤ c * (ε : ℝ)) (y : Y) :
    ∃ family : Families T A hA Λ ℓ D t terminal root C sf,
      family.closedProduct = closedProduct ∧ family.equilibrium = equilibrium ∧
      ∃ δ : NNReal, 0 < δ ∧
        DerivedHG2Conclusions.ConclusionClauses T A hA Λ ℓ D t terminal root C sf family geometry δ := by
  have hwindow : ∀ᶠ ε : NNReal in 𝓝[>] 0, ε ≤ min F.window G.window :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (lt_min F.window_positive G.window_positive))
  have hAt : ∀ s N, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε) := by
    intro s N
    filter_upwards [produced s N, actual, auxiliary, invariant s N, hwindow] with ε hp ha hy hi hwin
    intro hε
    let productAt := Classical.choice (hp hε)
    let νY := Classical.choose (hy hε hwin)
    have gapY := Classical.choose_spec (hy hε hwin)
    have actualε := ha hε hwin
    have hP := levels_positive_compact T A Λ ℓ N D ((terminal s).val + 1)
      (by omega) (by have h := (terminal s).isLt; omega)
    have descended := RepresentedProductPrefixGap.exists_original_prefix_gap
      F G L L' ε hε hwin (actualPrefix T A Λ ℓ D (terminal s) N) A hP hA w hw R hR bound
      nonnegative (C ε) (sf ε hε) actualε.1 (CP ε) (sfP ε hε) actualε.2
      (actualPrefix (T.prodCongr S) AP LP ℓ DP (terminal s) N)
      (ambient_levels_measurable (T.prodCongr S) AP hAP LP ℓ N DP ((terminal s).val + 1))
      (ProductAdaptedFiltration.actualPrefix_product T S A Λ ℓ D (terminal s) N)
      νY gapY productAt.data (Λ (D.index (selectedIndex ℓ t terminal root s)))
      (core_live s) productAt.positive y
    let dp := Classical.choose descended
    have hd := Classical.choose_spec descended
    apply MarginalPrefixAssembly.assemble_at T A hA Λ ℓ D t terminal root C sf closedProduct
      s N ε hε dp (hi hε) hd.1
      ((productMeasure _ _ productAt.data).map Subtype.val) ?_ productAt.support ?_ y
    · rw [Measure.map_map measurable_fst measurable_subtype_coe]
      exact hd.2
    · intro hN
      have hb := congrArg (fun μ : Measure (X × Y) => μ.map Prod.fst) (productAt.base_identity hN)
      rw [Measure.map_map measurable_fst measurable_subtype_coe,
        Measure.map_map measurable_fst measurable_subtype_coe] at hb
      rw [Measure.map_map measurable_fst measurable_subtype_coe]
      exact hb.trans (marginal s ε).symm
  have hzero : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x A = 0 := by
    intro ε _hε x
    let : IsProbabilityMeasure (geometry.noise ε) := geometry.probability ε
    rw [geometry.actual_model ε]
    exact ActualAbsorbingKernelSupport.target_absorbing_mass_zero (geometry.noise ε)
      (geometry.maps ε) (geometry.measurable ε) A hA.measurableSet
      (fun x => Real.exp (geometry.potential x))
      (Real.measurable_exp.comp geometry.potential_measurable)
      geometry.R geometry.R_positive geometry.weight_bound x
  obtain ⟨family, hproducts, hequilibrium⟩ :=
    AssembleExactPrefixFamilies.families_of_produced_prefixes T A hA Λ ℓ D t terminal root C sf
      closedProduct hAt hzero hcore horder hprob equilibrium localWeak
  obtain ⟨δ, hδ, hclauses⟩ := DerivedHG2Conclusions.conditional_global_global
    T A hA Λ ℓ D t terminal root C sf family geometry hℓ c hc hnoise
  exact ⟨family, hproducts, hequilibrium, δ, hδ, hclauses⟩

end ConditionedStochasticStabilityHyperbolic.Global.StabilizedShiftedPrefixApplication
