module

public import ConditionedStochasticStabilityHyperbolic.Global.AssembleShiftedPrefixFamilies

/-! The actual selected products and equilibrium family are retained by
explicit identities when selecting all shifted spectral witnesses. -/
public noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.AssembleExactPrefixFamilies
open AbsorbingMarkovChains LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry
open ActualFiltrationGrowth FiltrationPressureConfinement ComplexStrongFeller RestrictedLayerChain
open LayerQuasiErgodic DerivedHG2Application AssembleShiftedPrefixFamilies
variable {X I : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λ : I → Set X) (ℓ : ℕ)
  (D : AdaptedSource T A Λ ℓ) (t : ℕ) (terminal : Fin t → Fin ℓ)
  (root : ∀ s, Fin ((terminal s).val + 1))
  (C : NNReal → CanonicalChain X) (sf : ∀ ε, 0 < ε → HasStrongFellerKernel (C ε))

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
    ∃ family : Families T A hA Λ ℓ D t terminal root C sf,
      family.closedProduct = closedProduct ∧ family.equilibrium = equilibrium := by
  have hwindows : ∀ s N, ∃ δ : NNReal, 0 < δ ∧ ∀ ε, 0 < ε → ε < δ →
      ∀ hε : 0 < ε, Nonempty (At T A hA Λ ℓ D t terminal root C sf closedProduct s N ε hε) := by
    intro s N
    exact window_of_eventually _ (hproduced s N)
  choose window hwindow hwin using hwindows
  let witness (s : Fin t) (N : ℕ) (ε : NNReal) (hε : 0 < ε) (hs : ε < window s N) :=
    Classical.choice (hwin s N ε hε hs hε)
  let family : Families T A hA Λ ℓ D t terminal root C sf := {
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
  }
  exact ⟨family, rfl, rfl⟩

end ConditionedStochasticStabilityHyperbolic.Global.AssembleExactPrefixFamilies
