module

public import ConditionedStochasticStabilityHyperbolic.Global.ClosedDominantProduct
public import ConditionedStochasticStabilityHyperbolic.Global.TwoSidedSelectedQuasiErgodic

/-! # Actual global selected QEM from a produced closed-local source

No diagonal gap, global QEM or product correspondence is supplied. Closed
local data is transported through the actual conull stratum, then combined
with the lower and upper aggregate growth estimates. Those estimates are
provided by the checked finite pressure/KL and literal filtration producers.
-/
@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ClosedSelectedQuasiErgodic
open ComplexStrongFeller RestrictedLayerChain NestedLayerKernel LayerQuasiErgodic
open ClosedDominantSource ClosedDominantProduct MiddleStratumLeadingData
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (L0 L1 : Set X) (hL0 : MeasurableSet L0) (hL1 : MeasurableSet L1) (h01 : L0 ⊆ L1)

include h01 in
/-- Closed-local producers and actual subordinate growth yield the actual
selected global physical probability, core support and qualified uniqueness. -/
theorem exists_selected_QEM_from_closed_local
    (hs0 : ∀ x ∈ L0, C.killedTransition x L0ᶜ = 0)
    (hs1 : ∀ x ∈ L1, ∀ᵐ y ∂C.killedTransition x, y ∈ L1)
    (hzero : ∀ x : (closure (L1 \ L0) : Set X),
      (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1)).killedTransition x
        (innerLevel (L1 \ L0) (closure (L1 \ L0)))ᶜ = 0)
    (d : RankOneSpectralData
      (transferOperator (𝕜 := ℝ) (chain C (closure (L1 \ L0)) (closureLayer_measurable L0 L1))
        (strongFeller C hSF (closure (L1 \ L0)) (closureLayer_measurable L0 L1)))
      (1 : (closure (L1 \ L0) : Set X) →ᵇ ℝ))
    {CA CD βA βD : ℝ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hβA : 0 ≤ βA) (hβD : 0 ≤ βD) (hArate : βA < d.rate) (hDrate : βD < d.rate)
    (hA : ∀ n : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L0 hL0)
      (strongFeller C hSF L0 hL0) ^ n‖ ≤ CA * βA ^ n)
    (hD : ∀ n : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L1ᶜ hL1.compl)
      (strongFeller C hSF L1ᶜ hL1.compl) ^ n‖ ≤ CD * βD ^ n)
    (μ : Measure (closure (L1 \ L0) : Set X)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (closure (L1 \ L0) : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y)
    (Λ : Set (L1 \ L0 : Set X)) (hΛ : Λ.Nonempty)
    (hΛpos : ∀ y ∈ Λ, 0 < d.eigenvector ⟨y.val, subset_closure y.property⟩)
    (hΛsupport : ∀ y ∈ Λ, (⟨y.val, subset_closure y.property⟩ : (closure (L1 \ L0) : Set X)) ∈
      (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = d.rate ∧ C.IsQuasiErgodic (productMeasure C hSF dg) ∧
      productMeasure C hSF dg = (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      Subtype.val '' Λ ⊆ (productMeasure C hSF dg).support ∧
      (∀ ν : Measure X, C.IsQuasiErgodic ν → Subtype.val '' Λ ⊆ ν.support →
        ν = productMeasure C hSF dg) ∧
      (∀ y : (L1 \ L0 : Set X), dg.eigenvector y.val =
        d.rate⁻¹ * d.eigenvector ⟨y.val, subset_closure y.property⟩) ∧
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x,
        0 < dg.eigenvector x → Tendsto (MeasurableCanonical.pathAverage C f x) atTop
          (𝓝 (∫ y, f y ∂productMeasure C hSF dg)) := by
  let dm := dominantData C hSF L0 L1 hL0 hL1 hzero d
  let μm := dominantMeasure C hSF L0 L1 d μ
  let : IsFiniteMeasure μm := dominantMeasure_finite C hSF L0 L1 hL0 hL1 d μ
  let Λm := middlePoint L0 L1 '' Λ
  have hm : ∀ f, dm.mean f = ∫ y, f y ∂μm :=
    dominant_represents C hSF L0 L1 hL0 hL1 hzero d μ hmean
  have hnonneg : ∀ y, 0 ≤ dm.eigenvector y := by
    intro y
    let p : (L1 \ L0 : Set X) := ⟨y.val.val, y.val.property, y.property⟩
    have hy : middlePoint L0 L1 p = y := by apply Subtype.ext; apply Subtype.ext; rfl
    rw [← hy, dominant_vector C hSF L0 L1 hL0 hL1 hzero d p]
    exact mul_nonneg (inv_nonneg.mpr d.rate_pos.le) (hg0 _)
  have hpos : ∀ y ∈ Λm, 0 < dm.eigenvector y := by
    rintro _ ⟨p, hp, rfl⟩
    rw [dominant_vector C hSF L0 L1 hL0 hL1 hzero d p]
    exact mul_pos (inv_pos.mpr d.rate_pos) (hΛpos p hp)
  have hsupport : Λm ⊆ (LeanShared.eigenvectorMeasure μm dm.eigenvector).support := by
    rintro _ ⟨p, hp, rfl⟩
    exact dominant_core_support C hSF L0 L1 hL0 hL1 hzero d μ hmean p (hΛsupport p hp)
  have hrate := dominant_rate C hSF L0 L1 hL0 hL1 hzero d
  obtain ⟨dg, hgrate, hq, hproduct, hsupp, huniq, hv, hlim⟩ :=
    TwoSidedSelectedQuasiErgodic.exists_actual_selected_QEM_from_two_aggregates
      C hSF L0 L1 hL0 hL1 h01 hs0 hs1 dm hCA hCD hβA hβD
      (hArate.trans_eq hrate.symm) (hDrate.trans_eq hrate.symm) hA hD
      μm hm hnonneg Λm (hΛ.image _) hpos hsupport
  have himage : (fun y : ((innerLevel L0 L1)ᶜ : Set L1) => y.val.val) '' Λm =
      Subtype.val '' Λ := by
    ext x
    constructor
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨middlePoint L0 L1 p, ⟨p, hp, rfl⟩, rfl⟩
  refine ⟨dg, hgrate.trans hrate, hq, ?_, ?_, ?_, ?_, hlim⟩
  · exact hproduct.trans (dominant_product_map_eq_closed C hSF L0 L1 hL0 hL1 hzero d μ hmean)
  · exact himage ▸ hsupp
  · intro ν hν hνsupport
    exact huniq ν hν (himage.symm ▸ hνsupport)
  · intro p
    exact (hv (middlePoint L0 L1 p)).trans
      (dominant_vector C hSF L0 L1 hL0 hL1 hzero d p)

end ConditionedStochasticStabilityHyperbolic.Global.ClosedSelectedQuasiErgodic
