module

public import ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationQuasiErgodic
public import ConditionedStochasticStabilityHyperbolic.Global.PrefixQuasiErgodic

/-!
# Selected HG2 prefix produces an actual full-process QEM

The selected local leading theorem and actual subordinate stratum estimates
produce the prefix gap and probability internally. Invariance of the prefix
then makes this a genuine QEM for the original fixed-absorption chain, with
exact local-product correspondence and full-process starting-state limits.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.SelectedPrefixPackage
open ComplexStrongFeller LayerOperators RestrictedLayerChain LayerQuasiErgodic
open RelativeFiltrationQuasiErgodic PrefixCorrespondence PrefixQuasiErgodic
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U) [CompactSpace U]

/-- One selected pressure block's actual local data and literal lower
subordinate filtration produce the original fixed-A process QEM and its
pointwise conditioned limits. No target QEM or full-process gap is assumed. -/
theorem exists_actual_package_for_selected_prefix
    (hprefix : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (L : Set U) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂(chain C U hU).killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) (chain C U hU)
      (strongFeller C hSF U hU) L hL) (1 : (Lᶜ : Set U) →ᵇ ℝ))
    {β : ℝ} (hβ : 0 < β) (hβrate : β < d.rate) (n : ℕ)
    (M : ℕ → Set U) (hM : ∀ i, MeasurableSet (M i)) (hzero : M 0 = ∅)
    (hnested : ∀ i, M i ⊆ M (i + 1)) (hterminal : M n = L)
    (hnoUp : ∀ i, i ≤ n → ∀ x ∈ M i,
      (chain C U hU).killedTransition x (M n \ M i) = 0)
    (hleaf : ∀ i, i < n → ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      ‖transferOperator (𝕜 := ℝ) (chain (chain C U hU) (M (i + 1) \ M i)
        ((hM (i + 1)).diff (hM i)))
        (strongFeller (chain C U hU) (strongFeller C hSF U hU)
          (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i))) ^ m‖ ≤ K * β ^ m)
    (μ : Measure (Lᶜ : Set U)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (Lᶜ : Set U) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (Λ : Set (Lᶜ : Set U))
    (hΛ : Λ.Nonempty) (hΛpos : ∀ y ∈ Λ, 0 < d.eigenvector y)
    (hΛsupport : Λ ⊆ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C U hU)
        (strongFeller C hSF U hU)) (1 : U →ᵇ ℝ),
      dg.rate = d.rate ∧ restrictOperator Lᶜ dg.eigenvector = d.eigenvector ∧
      C.IsQuasiErgodic ((productMeasure (chain C U hU) (strongFeller C hSF U hU) dg).map Subtype.val) ∧
      (productMeasure (chain C U hU) (strongFeller C hSF U hU) dg).map Subtype.val =
        (LeanShared.eigenvectorMeasure μ d.eigenvector).map
          (fun y : (Lᶜ : Set U) => y.val.val) ∧
      ∀ f : X → ℝ, Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x : U,
        0 < dg.eigenvector x →
        Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
          (𝓝 (∫ y, f y ∂(LeanShared.eigenvectorMeasure μ d.eigenvector).map
            (fun y : (Lᶜ : Set U) => y.val.val))) := by
  obtain ⟨dg, hrate, hrestrict, hq, hprod, _hcore, _hunique, _hlim⟩ :=
    global_package_from_relative_lower_filtration (chain C U hU) (strongFeller C hSF U hU)
      L hL hsupport d hβ hβrate n M hM hzero hnested hterminal hnoUp hleaf
      μ hmean hg0 Λ hΛ hΛpos hΛsupport
  have hmap : (productMeasure (chain C U hU) (strongFeller C hSF U hU) dg).map Subtype.val =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map
        (fun y : (Lᶜ : Set U) => y.val.val) := by
    rw [hprod, Measure.map_map measurable_subtype_coe measurable_subtype_coe]
    rfl
  refine ⟨dg, hrate, hrestrict, full_process_isQuasiErgodic_of_prefix C U hU hprefix _ hq, hmap, ?_⟩
  intro f hf hb x hx
  rw [← hmap]
  exact full_process_limit_from_prefix C U hU hprefix (strongFeller C hSF U hU) dg f hf hb x hx

end ConditionedStochasticStabilityHyperbolic.Global.SelectedPrefixPackage
