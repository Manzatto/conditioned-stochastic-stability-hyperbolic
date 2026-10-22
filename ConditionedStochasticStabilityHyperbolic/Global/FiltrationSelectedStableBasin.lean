module

public import ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedStableBasin
public import ConditionedStochasticStabilityHyperbolic.Global.ActualPrefixBasicGeometry

/-! # Actual stable-basin limits from literal selected-prefix geometry

The geometric data is the very same adapted filtration used to construct the
selected prefix spectral gap. Compactness, two-sided basic invariance, prefix
interior containment and all live-path conditions are derived. The remaining
geometric source inputs are ordinary basic transitivity and metric heteroclinic
connections, together with the genuine noise image-ball hypothesis.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.FiltrationSelectedStableBasin
open AbsorbingMarkovChains ComplexStrongFeller LayerOperators RestrictedLayerChain
open LayerQuasiErgodic AmbientPrefixEigenfunction PrefixCorrespondence
open LeanShared.ControlledPlaqueClosure HeteroclinicAccessibility
open LeanShared FiltrationLayerGeometry ShiftedFiltrationGeometry ActualPrefixBasicGeometry
variable {X Ω I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (T : X ≃ₜ X) (A : Set X) (hA : IsOpen A) (Λbasic : I → Set X) (ℓ N : ℕ)
  (D : AdaptedSource T A Λbasic ℓ) (hsep : ∀ j, Λbasic j ⊆ interior Aᶜ)
  (k : ℕ) (hkpos : 0 < k) (hk : k ≤ ℓ)
variable (C : CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (hU : MeasurableSet (levels T A Λbasic ℓ N D k)) [CompactSpace (levels T A Λbasic ℓ N D k)]

include hA hsep hkpos in
theorem full_conditioned_limit_from_literal_prefix_geometry
    (hprefix : ∀ x ∈ (levels T A Λbasic ℓ N D k), C.killedTransition x (levels T A Λbasic ℓ N D k)ᶜ = 0)
    (dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C (levels T A Λbasic ℓ N D k) hU)
      (strongFeller C hSF (levels T A Λbasic ℓ N D k) hU)) (1 : (levels T A Λbasic ℓ N D k) →ᵇ ℝ))
    (Λ : Set (levels T A Λbasic ℓ N D k)) (hΛpos : ∀ y ∈ Λ, 0 < dg.eigenvector y)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (V : Set X) (hV : MeasurableSet V) (O : Set X) (hO : IsOpen O) (hOV : O ⊆ V) (φ : X → ℝ) (hφ : Measurable φ)
    (W : ℝ) (hW : 0 < W) (hbound : ∀ x, Real.exp (φ x) ≤ W)
    (hmodel : C.killedTransition = (NoiseKernel.chain ρ F hF V hV
      (fun x => Real.exp (φ x)) (Real.measurable_exp.comp hφ) W hW hbound).killedTransition)
    (hstrict : MapsTo T (closure A) A) (hOactual : O = interior Aᶜ)
    (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (htrans : ∀ i, forwardTransitiveOn T ((basicFamily T A Λbasic ℓ D k hk) i))
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ (levels T A Λbasic ℓ N D k) ∩ O, ∀ y ∈ (levels T A Λbasic ℓ N D k) ∩ O, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (edge : Fin k → Fin k → Prop)
    (hedge : ∀ i j, edge i j → ∃ z : X,
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ (basicFamily T A Λbasic ℓ D k hk) j,
        dist ((T : X → X)^[n + 1] z) y < r) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ (basicFamily T A Λbasic ℓ D k hk) i,
        dist ((T.symm : X → X)^[n] z) y < r))
    {i root : Fin k} (hreach : Relation.ReflTransGen edge i root)
    (hroot : (basicFamily T A Λbasic ℓ D k hk) root = Subtype.val '' Λ) (x : (levels T A Λbasic ℓ N D k))
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ (basicFamily T A Λbasic ℓ D k hk) i,
      dist ((T : X → X)^[n + 1] x.val) y < r)
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) :
    Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
      (𝓝 (∫ y, f y ∂(productMeasure (chain C (levels T A Λbasic ℓ N D k) hU) (strongFeller C hSF (levels T A Λbasic ℓ N D k) hU) dg).map Subtype.val)) := by
  have hp := actual_prefix_basic_properties T A hA Λbasic ℓ N D hsep k hk
  have hFamilyV : ∀ i, (basicFamily T A Λbasic ℓ D k hk) i ⊆ (levels T A Λbasic ℓ N D k) ∩ O := by
    intro i y hy
    have hm := (hp i).2.2.2 hy
    exact ⟨interior_subset hm.1, hOactual.symm ▸ hm.2⟩
  exact ActualSelectedStableBasin.full_conditioned_limit_of_actual_selected_stable_basin
    C hSF (levels T A Λbasic ℓ N D k) hU hprefix dg Λ hΛpos ρ F hF hFc V hV O hO hOV φ hφ W hW hbound
    hmodel T A hstrict (levels_positive_adapted T A Λbasic ℓ N D k hkpos hk)
    hOactual ω₀ hzero (basicFamily T A Λbasic ℓ D k hk) hFamilyV (fun i => (hp i).2.1) (fun i => (hp i).2.2.1)
    htrans (fun i => (hp i).1) (fun i y hy => ((hp i).2.2.2 hy).1)
    hδ himage edge hedge hreach hroot x happroach f hf hb

end ConditionedStochasticStabilityHyperbolic.Global.FiltrationSelectedStableBasin
