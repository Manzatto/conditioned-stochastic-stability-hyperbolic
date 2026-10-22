module

public import ConditionedStochasticStabilityHyperbolic.Global.RepresentedProductPrefixGap
public import ConditionedStochasticStabilityHyperbolic.Global.MarginalPrefixAssembly
public import ConditionedStochasticStabilityHyperbolic.Global.ProductAdaptedFiltration
public import ConditionedStochasticStabilityHyperbolic.Global.SinglePrefixStabilityConclusion

/-! The single unshifted prefix used by HG1. Derived product-prefix and
canonical local-family outputs give the SAME original global QEM family and
its weak equilibrium limit. No all-shift or stable-basin assumptions are
needed. This output-consumer is used inside the ordinary-source frontend. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.StabilizedSinglePrefixApplication
open LeanShared Paper Paper.RegularNoise Paper.ActualProductRestrictedChain
open ComplexStrongFeller LayerQuasiErgodic ShiftedFiltrationGeometry ActualFiltrationGrowth
open DerivedHG2Application AssembleShiftedPrefixFamilies FiltrationPressureConfinement
variable {X Y E H I ι κ : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [MetricSpace X] [CompactSpace X] [MetricSpace Y] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [SecondCountableTopology X] [SecondCountableTopology Y]
  [ChartedSpace E X] [ChartedSpace H Y]
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

omit [SecondCountableTopology X] in
include nonnegative sf sfP in
set_option maxHeartbeats 1600000 in

/-- Descend the actual produced product data and retain the canonical
original marginal family, including weak convergence and core support. -/
theorem same_family
    (localFamily : ∀ q, NNReal → ProbabilityMeasure
      (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root q)))
    (closedProductP : ∀ q, NNReal → Measure
      (closedLayer (T.prodCongr S) AP LP ℓ 0 DP (selectedIndex ℓ t terminal root q)))
    (s : Fin t) (νeq : ProbabilityMeasure X)
    (weak : Tendsto (fun ε => ProbabilityMeasure.map (localFamily s ε) Subtype.val)
      (𝓝[>] 0) (𝓝 νeq))
    (produced : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At (T.prodCongr S) AP hAP LP ℓ DP t terminal root CP sfP closedProductP s 0 ε hε))
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
    (invariant : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε,
      ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) 0,
        (C ε).killedTransition x (actualPrefix T A Λ ℓ D (terminal s) 0)ᶜ = 0)
    (core_live : Λ (D.index (selectedIndex ℓ t terminal root s)) ⊆ Aᶜ)
    (marginal : ∀ ε, (localFamily s ε : Measure (closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))).map Subtype.val =
      (closedProductP s ε).map (fun z => z.val.1)) (y : Y) :
    ∃ ν : NNReal → ProbabilityMeasure X,
      Tendsto ν (𝓝[>] 0) (𝓝 νeq) ∧
      (∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ _hε : 0 < ε,
        (C ε).IsQuasiErgodic (ν ε : Measure X) ∧
          Λ (D.index (selectedIndex ℓ t terminal root s)) ⊆ (ν ε : Measure X).support) ∧
      ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
        Nonempty (At T A hA Λ ℓ D t terminal root C sf
          (fun q ε => (localFamily q ε : Measure _)) s 0 ε hε) := by
  have hwindow : ∀ᶠ ε : NNReal in 𝓝[>] 0, ε ≤ min F.window G.window :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (lt_min F.window_positive G.window_positive))
  have hAt : ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf
        (fun q ε => (localFamily q ε : Measure _)) s 0 ε hε) := by
    filter_upwards [produced, actual, auxiliary, invariant, hwindow] with ε hp ha hy hi hwin
    intro hε
    let productAt := Classical.choice (hp hε)
    let νY := Classical.choose (hy hε hwin)
    have gapY := Classical.choose_spec (hy hε hwin)
    have actualε := ha hε hwin
    have hP := levels_positive_compact T A Λ ℓ 0 D ((terminal s).val + 1)
      (by omega) (by have h := (terminal s).isLt; omega)
    have descended := RepresentedProductPrefixGap.exists_original_prefix_gap
      F G L L' ε hε hwin (actualPrefix T A Λ ℓ D (terminal s) 0) A hP hA w hw R hR bound
      nonnegative (C ε) (sf ε hε) actualε.1 (CP ε) (sfP ε hε) actualε.2
      (actualPrefix (T.prodCongr S) AP LP ℓ DP (terminal s) 0)
      (ambient_levels_measurable (T.prodCongr S) AP hAP LP ℓ 0 DP ((terminal s).val + 1))
      (ProductAdaptedFiltration.actualPrefix_product T S A Λ ℓ D (terminal s) 0)
      νY gapY productAt.data (Λ (D.index (selectedIndex ℓ t terminal root s)))
      core_live productAt.positive y
    let dp := Classical.choose descended
    have hd := Classical.choose_spec descended
    apply MarginalPrefixAssembly.assemble_at T A hA Λ ℓ D t terminal root C sf
      (fun q ε => (localFamily q ε : Measure _)) s 0 ε hε dp (hi hε) hd.1
      ((productMeasure _ _ productAt.data).map Subtype.val) ?_ productAt.support ?_ y
    · rw [Measure.map_map measurable_fst measurable_subtype_coe]
      exact hd.2
    · intro hN
      have hb := congrArg (fun μ : Measure (X × Y) => μ.map Prod.fst) (productAt.base_identity hN)
      rw [Measure.map_map measurable_fst measurable_subtype_coe,
        Measure.map_map measurable_fst measurable_subtype_coe] at hb
      rw [Measure.map_map measurable_fst measurable_subtype_coe]
      exact hb.trans (marginal ε).symm

  obtain ⟨ν, hweak, hqem⟩ := SinglePrefixStabilityConclusion.same_family
    T A hA Λ ℓ D t terminal root C sf localFamily s νeq weak hAt
  exact ⟨ν, hweak, hqem, hAt⟩

end ConditionedStochasticStabilityHyperbolic.Global.StabilizedSinglePrefixApplication
