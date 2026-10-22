module

public import ConditionedStochasticStabilityHyperbolic.Global.ProducedSelectedPrefix
public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Application
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComparedLocalQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.DerivedHG2Conclusions

/-!
# Simultaneous assembly of the produced shifted-prefix families

This is dependent-choice assembly of produced prefix outputs,
not a classical source assumption. In the actual application the pointwise
witness comes from ProducedSelectedPrefix and local product uniqueness. Windows may depend on the shift, as required for arbitrary stable starts.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter Function Metric
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies
open AbsorbingMarkovChains LeanShared ShiftedFiltrationGeometry ActualFiltrationGrowth
open ComplexStrongFeller RestrictedLayerChain LayerQuasiErgodic DerivedHG2Application
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))

local instance prefixCompact (s : Fin t) (N : ℕ) : CompactSpace (actualPrefix T A Λ ℓ D (terminal s) N) :=
  isCompact_iff_compactSpace.mp (levels_positive_compact T A Λ ℓ N D ((terminal s).val + 1) (by omega) (by have h := (terminal s).isLt; omega))

abbrev selectedIndex (s : Fin t) : Fin ℓ :=
  ⟨(root s).val, by have h := (root s).isLt; have hh := (terminal s).isLt; omega⟩

/-- A produced prefix output at one actual positive noise. -/
structure At
    (closedProduct : ∀ s, NNReal → Measure (FiltrationPressureConfinement.closedLayer T A Λ ℓ 0 D
      (selectedIndex ℓ t terminal root s))) (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε) where
  data : RankOneSpectralData (transferOperator (𝕜 := ℝ)
    (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) N)
      (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
    (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) N)
      (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1))))
    (1 : actualPrefix T A Λ ℓ D (terminal s) N →ᵇ ℝ)
  invariant : ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) N,
    (C ε).killedTransition x (actualPrefix T A Λ ℓ D (terminal s) N)ᶜ = 0
  positive : ∀ x : actualPrefix T A Λ ℓ D (terminal s) N,
    x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s)) → 0 < data.eigenvector x
  support : Λ (D.index (selectedIndex ℓ t terminal root s)) ⊆
    ((productMeasure _ _ data).map Subtype.val).support
  base_identity : N = 0 →
    (productMeasure _ _ data).map Subtype.val = (closedProduct s ε).map Subtype.val

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
private theorem window_of_eventually (P : NNReal → Prop)
    (h : ∀ᶠ ε : NNReal in 𝓝[>] 0, P ε) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ → P ε := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine ⟨Real.toNNReal r, Real.toNNReal_pos.mpr hr, ?_⟩
  intro ε hε hsmall
  apply hball
  refine ⟨?_, hε⟩
  change dist ε 0 < r
  simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg ε.coe_nonneg] using
    (show (ε : ℝ) < r from Real.lt_toNNReal_iff_coe_lt.mp hsmall)

omit [CompactSpace X] in
/-- Identify the internally produced closed product with the preferred local
weak family using its checked local QEM uniqueness. -/
theorem at_of_actual_produced_pair
    (closedProduct : ∀ s, NNReal → Measure (FiltrationPressureConfinement.closedLayer T A Λ ℓ 0 D
      (selectedIndex ℓ t terminal root s)))
    (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε)
    (dg : RankOneSpectralData (transferOperator (𝕜 := ℝ)
      (chain (C ε) (actualPrefix T A Λ ℓ D (terminal s) N)
        (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1)))
      (strongFeller (C ε) (sf ε hε) (actualPrefix T A Λ ℓ D (terminal s) N)
        (ambient_levels_measurable T A hA Λ ℓ N D ((terminal s).val + 1))))
      (1 : actualPrefix T A Λ ℓ D (terminal s) N →ᵇ ℝ))
    (hinvariant : ∀ x ∈ actualPrefix T A Λ ℓ D (terminal s) N,
      (C ε).killedTransition x (actualPrefix T A Λ ℓ D (terminal s) N)ᶜ = 0)
    (hpositive : ∀ x : actualPrefix T A Λ ℓ D (terminal s) N,
      x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s)) → 0 < dg.eigenvector x)
    (hsupport : Λ (D.index (selectedIndex ℓ t terminal root s)) ⊆
      ((productMeasure _ _ dg).map Subtype.val).support)
    (R : ℝ) (hR : 0 < R)
    (dc : RankOneSpectralData (R • transferOperator (𝕜 := ℝ)
      (chain (C ε) (FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s))
        (FiltrationPressureConfinement.closedLayer_measurable T A Λ ℓ N D (selectedIndex ℓ t terminal root s)))
      (strongFeller (C ε) (sf ε hε) (FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s))
        (FiltrationPressureConfinement.closedLayer_measurable T A Λ ℓ N D (selectedIndex ℓ t terminal root s))))
      (1 : FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s) →ᵇ ℝ))
    (μ : Measure (FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s)))
    [IsFiniteMeasure μ] (hm : ∀ f, dc.mean f = ∫ y, f y ∂μ)
    (hproduct : (productMeasure _ _ dg).map Subtype.val = (eigenvectorMeasure μ dc.eigenvector).map Subtype.val)
    (hlocalUnique : N = 0 → ∀ ν : Measure (FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s)),
      (chain (C ε) (FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s))
        (FiltrationPressureConfinement.closedLayer_measurable T A Λ ℓ N D (selectedIndex ℓ t terminal root s))).IsQuasiErgodic ν →
      {x | x.val ∈ Λ (D.index (selectedIndex ℓ t terminal root s))} ⊆ ν.support →
      ν.map Subtype.val = (closedProduct s ε).map Subtype.val) :
    Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε) := by
  let K := FiltrationPressureConfinement.closedLayer T A Λ ℓ N D (selectedIndex ℓ t terminal root s)
  let hK := FiltrationPressureConfinement.closedLayer_measurable T A Λ ℓ N D (selectedIndex ℓ t terminal root s)
  let CL := chain (C ε) K hK
  let sfl := strongFeller (C ε) (sf ε hε) K hK
  have heq : R⁻¹ • (R • transferOperator (𝕜 := ℝ) CL sfl) = transferOperator CL sfl := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hR), one_smul]
  let dn := dc.ofRawNormalization R hR heq
  have hmn : ∀ f : K →ᵇ ℝ, dn.mean f = ∫ y, f y ∂μ := by
    intro f
    simpa only [dn, RankOneSpectralData.ofRawNormalization_mean] using hm f
  have hgn := dn.eigenvector_nonneg_of_positive (LayerRankOne.actual_transfer_positive CL sfl)
  have hqn := QuasiErgodic.eigenvectorMeasure_isQuasiErgodic_of_strongFeller CL
    (transferOperator CL sfl) (transferOperator_apply CL sfl) dn μ hmn hgn sfl
  have hq : CL.IsQuasiErgodic (eigenvectorMeasure μ dc.eigenvector) := by
    simpa only [dn, RankOneSpectralData.ofRawNormalization_eigenvector] using hqn
  refine ⟨{
    data := dg
    invariant := hinvariant
    positive := hpositive
    support := hsupport
    base_identity := ?_
  }⟩
  intro hN
  apply hproduct.trans
  apply hlocalUnique hN _ hq
  intro x hx
  apply ComparedLocalQuasiErgodic.mem_support_of_mem_support_map K (eigenvectorMeasure μ dc.eigenvector) x
  rw [← hproduct]
  exact hsupport hx

omit [CompactSpace X] in
/-- Select all shift-dependent windows and spectral data simultaneously.
The local weak family and its exact base products are preserved. -/
theorem families_of_produced_prefixes
    (closedProduct : ∀ s, NNReal → Measure (FiltrationPressureConfinement.closedLayer T A Λ ℓ 0 D
      (selectedIndex ℓ t terminal root s)))
    (hproduced : ∀ s N, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε))
    (hzero : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x A = 0)
    (hcore : ∀ s, (Λ (D.index (selectedIndex ℓ t terminal root s))).Nonempty)
    (horder : ∀ s q : Fin t, s < q → (terminal q).val + 1 ≤ (root s).val)
    (hprob : ∀ s ε, IsProbabilityMeasure (closedProduct s ε))
    (equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ))
    (hweak : ∀ s, Tendsto
      (fun ε => ProbabilityMeasure.map
        (⟨closedProduct s ε, hprob s ε⟩ : ProbabilityMeasure
          (FiltrationPressureConfinement.closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))) Subtype.val)
      (𝓝[>] 0) (𝓝 (ProbabilityMeasure.map (equilibrium s) (Subtype.val : ↥(Aᶜ) → X)))) :
    Nonempty (Families T A hA Λ ℓ D t terminal root C sf) := by
  have hwindows : ∀ s N, ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
      ∀ hε : 0 < ε, Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε) := by
    intro s N
    exact window_of_eventually _ (hproduced s N)
  choose window hwindow hwin using hwindows
  let witness (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε) (hs : ε < window s N) :=
    Classical.choice (hwin s N ε hε hs hε)
  exact ⟨{
    window := window
    window_positive := hwindow
    data := fun s N ε hε hs => (witness s N ε hε hs).data
    invariant := fun s N ε hε hs => (witness s N ε hε hs).invariant
    zero_absorbing := hzero
    core_nonempty := hcore
    core_positive := fun s N ε hε hs => (witness s N ε hε hs).positive
    core_support := fun s N ε hε hs => (witness s N ε hε hs).support
    closedProduct := closedProduct
    base_product_identity := fun s ε hε hs => (witness s 0 ε hε hs).base_identity rfl
    root_above_later := horder
    closedProduct_probability := hprob
    equilibrium := equilibrium
    localWeak := hweak
  }⟩

/-- Named conditional HG2 application after all shifted physical-prefix outputs have been produced. -/
theorem conditional_global_global_from_produced_shifted_prefixes
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    (closedProduct : ∀ s, NNReal → Measure (FiltrationPressureConfinement.closedLayer T A Λ ℓ 0 D
      (selectedIndex ℓ t terminal root s)))
    (hproduced : ∀ s N, ∀ᶠ ε : NNReal in 𝓝[>] 0, ∀ hε : 0 < ε,
      Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε))
    (hzero : ∀ ε, 0 < ε → ∀ x, (C ε).killedTransition x A = 0)
    (hcore : ∀ s, (Λ (D.index (selectedIndex ℓ t terminal root s))).Nonempty)
    (horder : ∀ s q : Fin t, s < q → (terminal q).val + 1 ≤ (root s).val)
    (hprob : ∀ s ε, IsProbabilityMeasure (closedProduct s ε))
    (equilibrium : Fin t → ProbabilityMeasure ↥(Aᶜ))
    (hweak : ∀ s, Tendsto
      (fun ε => ProbabilityMeasure.map
        (⟨closedProduct s ε, hprob s ε⟩ : ProbabilityMeasure
          (FiltrationPressureConfinement.closedLayer T A Λ ℓ 0 D (selectedIndex ℓ t terminal root s))) Subtype.val)
      (𝓝[>] 0) (𝓝 (ProbabilityMeasure.map (equilibrium s) (Subtype.val : ↥(Aᶜ) → X))))
    (geometry : DerivedHG2Basins.GeometricSources (Ω := Ω) T A hA Λ ℓ D t terminal root C)
    (hℓ : 0 < ℓ) (c : ℝ) (hc : 0 ≤ c)
    (hnoise : ∀ ε : NNReal, 0 < ε → ∀ z ω,
      dist (geometry.maps ε (z, ω)) (T z) ≤ c * (ε : ℝ)) :
    ∃ family : Families T A hA Λ ℓ D t terminal root C sf,
      ∃ δ : NNReal, 0 < δ ∧
        DerivedHG2Conclusions.ConclusionClauses T A hA Λ ℓ D t terminal root C sf family geometry δ := by
  obtain ⟨family⟩ := families_of_produced_prefixes T A hA Λ ℓ D t terminal root C sf
    closedProduct hproduced hzero hcore horder hprob equilibrium hweak
  obtain ⟨δ, hδ, hclauses⟩ := DerivedHG2Conclusions.conditional_global_global
    T A hA Λ ℓ D t terminal root C sf family geometry hℓ c hc hnoise
  exact ⟨family, δ, hδ, hclauses⟩

end ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies
