module

public import ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationGrowth
public import ConditionedStochasticStabilityHyperbolic.Global.LayerProductCorrespondence
import Mathlib.Tactic.Linarith

/-!
# Finite subordinate layers produce the actual global QEM package

The literal nested filtration and actual disjoint-stratum bounds produce
aggregate growth internally. They then produce the global leading gap,
Riesz measure, QEM, local-product correspondence, support and qualified
uniqueness. No recursive coordinate certificate is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationQuasiErgodic

open ComplexStrongFeller LayerOperators RestrictedLayerChain
open RelativeFiltrationGrowth
open LayerRankOne LayerQuasiErgodic LayerProductCorrespondence

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)

omit [CompactSpace X] in
private theorem restriction_power_norm_congr (U V : Set X)
    (hU : MeasurableSet U) (hV : MeasurableSet V) (heq : U = V) (n : ℕ) :
    ‖transferOperator (𝕜 := ℝ) (chain C U hU) (strongFeller C hSF U hU) ^ n‖ =
      ‖transferOperator (𝕜 := ℝ) (chain C V hV) (strongFeller C hSF V hV) ^ n‖ := by
  subst V
  rfl

/-- A dominant upper local theorem and finitely many actual subordinate
lower layers give the global spectral/QEM/support/uniqueness package. -/
theorem global_package_from_relative_lower_filtration
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (upperOperator (𝕜 := ℝ) C hSF L hL)
      (1 : (Lᶜ : Set X) →ᵇ ℝ))
    {β : ℝ} (hβ : 0 < β) (hβrate : β < d.rate) (n : ℕ)
    (M : ℕ → Set X) (hM : ∀ i, MeasurableSet (M i)) (hzero : M 0 = ∅)
    (hnested : ∀ i, M i ⊆ M (i + 1)) (hterminal : M n = L)
    (hnoUp : ∀ i, i ≤ n → ∀ x ∈ M i, C.killedTransition x (M n \ M i) = 0)
    (hleaf : ∀ i, i < n → ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      ‖transferOperator (𝕜 := ℝ) (chain C (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i)))
        (strongFeller C hSF (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i))) ^ m‖ ≤ K * β ^ m)
    (μ : Measure (Lᶜ : Set X)) [IsFiniteMeasure μ]
    (hmean : ∀ f : (Lᶜ : Set X) →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (Λ : Set (Lᶜ : Set X))
    (hΛ : Λ.Nonempty) (hΛpos : ∀ y ∈ Λ, 0 < d.eigenvector y)
    (hΛsupport : Λ ⊆ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = d.rate ∧ restrictOperator Lᶜ dg.eigenvector = d.eigenvector ∧ C.IsQuasiErgodic (productMeasure C hSF dg) ∧
      productMeasure C hSF dg = (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      Subtype.val '' Λ ⊆ (productMeasure C hSF dg).support ∧
      (∀ ν : Measure X, C.IsQuasiErgodic ν → Subtype.val '' Λ ⊆ ν.support →
        ν = productMeasure C hSF dg) ∧
      ∀ (f : X → ℝ), Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x,
        0 < dg.eigenvector x →
        Tendsto (MeasurableCanonical.pathAverage C f x) atTop
          (𝓝 (∫ y, f y ∂productMeasure C hSF dg)) := by
  let γ := (β + d.rate) / 2
  have hβγ : β < γ := by dsimp [γ]; linarith
  have hγrate : γ < d.rate := by dsimp [γ]; linarith
  have hγ : 0 < γ := hβ.trans hβγ
  obtain ⟨CA, hCA, hpow⟩ := exists_literal_filtration_power_bound C hSF
    M hM hzero hnested 1 hβ n hnoUp (by simpa only [one_smul] using hleaf) hβγ
  simp only [one_smul] at hpow
  have hpow' : ∀ m : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C L hL)
      (strongFeller C hSF L hL) ^ m‖ ≤ CA * γ ^ m := by
    cases hterminal
    exact hpow
  have hA : ∀ m : ℕ, ‖lowerOperator (𝕜 := ℝ) C hSF L hL ^ m‖ ≤ CA * γ ^ m := by
    intro m
    rw [← transferOperator_eq_lower C hSF L hL]
    exact hpow' m
  let dg := globalDataWithSubordinateLower C hSF L hL hsupport d hCA hγ.le hγrate hA
  refine ⟨dg, lower_global_rate C hSF L hL hsupport d hCA hγ.le hγrate hA,
    lower_global_vector_restrict C hSF L hL hsupport d hCA hγ.le hγrate hA,
    productMeasure_isQuasiErgodic C hSF dg,
    lower_global_product_eq_local_map C hSF L hL hsupport d hCA hγ.le hγrate hA μ hmean hg0,
    lower_global_support_contains_local_core C hSF L hL hsupport d hCA hγ.le hγrate hA μ hmean hg0 Λ hΛsupport,
    ?_, ?_⟩
  · intro ν hq hsupp
    exact lower_global_qualified_uniqueness C hSF L hL hsupport d hCA hγ.le hγrate hA
      Λ hΛ hΛpos ν hq hsupp
  · intro f hf hb x hx
    exact conditioned_average_limit C hSF dg f hf hb x hx



/-- A dominant lower local theorem and finitely many actual subordinate
upper layers give the global spectral/QEM/support/uniqueness package. -/
theorem global_package_from_relative_upper_filtration
    (L : Set X) (hL : MeasurableSet L)
    (hsupport : ∀ x ∈ L, ∀ᵐ y ∂C.killedTransition x, y ∈ L)
    (d : RankOneSpectralData (lowerOperator (𝕜 := ℝ) C hSF L hL)
      (1 : L →ᵇ ℝ))
    {β : ℝ} (hβ : 0 < β) (hβrate : β < d.rate) (n : ℕ)
    (M : ℕ → Set X) (hM : ∀ i, MeasurableSet (M i)) (hzero : M 0 = ∅)
    (hnested : ∀ i, M i ⊆ M (i + 1)) (hterminal : M n = Lᶜ)
    (hnoUp : ∀ i, i ≤ n → ∀ x ∈ M i, C.killedTransition x (M n \ M i) = 0)
    (hleaf : ∀ i, i < n → ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ,
      ‖transferOperator (𝕜 := ℝ) (chain C (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i)))
        (strongFeller C hSF (M (i + 1) \ M i) ((hM (i + 1)).diff (hM i))) ^ m‖ ≤ K * β ^ m)
    (μ : Measure L) [IsFiniteMeasure μ]
    (hmean : ∀ f : L →ᵇ ℝ, d.mean f = ∫ y, f y ∂μ)
    (hg0 : ∀ y, 0 ≤ d.eigenvector y) (Λ : Set L)
    (hΛ : Λ.Nonempty) (hΛpos : ∀ y ∈ Λ, 0 < d.eigenvector y)
    (hΛsupport : Λ ⊆ (LeanShared.eigenvectorMeasure μ d.eigenvector).support) :
    ∃ dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) C hSF) (1 : X →ᵇ ℝ),
      dg.rate = d.rate ∧ restrictOperator L dg.eigenvector = d.eigenvector ∧ C.IsQuasiErgodic (productMeasure C hSF dg) ∧
      productMeasure C hSF dg = (LeanShared.eigenvectorMeasure μ d.eigenvector).map Subtype.val ∧
      Subtype.val '' Λ ⊆ (productMeasure C hSF dg).support ∧
      (∀ ν : Measure X, C.IsQuasiErgodic ν → Subtype.val '' Λ ⊆ ν.support →
        ν = productMeasure C hSF dg) ∧
      ∀ (f : X → ℝ), Measurable f → (∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) → ∀ x,
        0 < dg.eigenvector x →
        Tendsto (MeasurableCanonical.pathAverage C f x) atTop
          (𝓝 (∫ y, f y ∂productMeasure C hSF dg)) := by
  let γ := (β + d.rate) / 2
  have hβγ : β < γ := by dsimp [γ]; linarith
  have hγrate : γ < d.rate := by dsimp [γ]; linarith
  have hγ : 0 < γ := hβ.trans hβγ
  obtain ⟨CA, hCA, hpow⟩ := exists_literal_filtration_power_bound C hSF
    M hM hzero hnested 1 hβ n hnoUp (by simpa only [one_smul] using hleaf) hβγ
  simp only [one_smul] at hpow
  have hpow' : ∀ m : ℕ, ‖transferOperator (𝕜 := ℝ) (chain C Lᶜ hL.compl)
      (strongFeller C hSF Lᶜ hL.compl) ^ m‖ ≤ CA * γ ^ m := by
    intro m
    rw [← restriction_power_norm_congr C hSF (M n) Lᶜ (hM n) hL.compl hterminal m]
    exact hpow m
  have hA : ∀ m : ℕ, ‖upperOperator (𝕜 := ℝ) C hSF L hL ^ m‖ ≤ CA * γ ^ m := by
    intro m
    change ‖lowerOperator (𝕜 := ℝ) C hSF Lᶜ hL.compl ^ m‖ ≤ CA * γ ^ m
    rw [← transferOperator_eq_lower C hSF Lᶜ hL.compl]
    exact hpow' m
  let dg := globalDataWithSubordinateUpper C hSF L hL hsupport d hCA hγ.le hγrate hA
  refine ⟨dg, upper_global_rate C hSF L hL hsupport d hCA hγ.le hγrate hA,
    upper_global_vector_restrict C hSF L hL hsupport d hCA hγ.le hγrate hA,
    productMeasure_isQuasiErgodic C hSF dg,
    upper_global_product_eq_local_map C hSF L hL hsupport d hCA hγ.le hγrate hA μ hmean hg0,
    upper_global_support_contains_local_core C hSF L hL hsupport d hCA hγ.le hγrate hA μ hmean hg0 Λ hΛsupport,
    ?_, ?_⟩
  · intro ν hq hsupp
    exact upper_global_qualified_uniqueness C hSF L hL hsupport d hCA hγ.le hγrate hA
      Λ hΛ hΛpos ν hq hsupp
  · intro f hf hb x hx
    exact conditioned_average_limit C hSF dg f hf hb x hx



end ConditionedStochasticStabilityHyperbolic.Global.RelativeFiltrationQuasiErgodic
