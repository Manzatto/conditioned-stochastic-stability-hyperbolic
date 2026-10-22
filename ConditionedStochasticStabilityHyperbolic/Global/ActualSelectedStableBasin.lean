module

public import ConditionedStochasticStabilityHyperbolic.Global.SelectedGlobalBasin
public import ConditionedStochasticStabilityHyperbolic.Global.ActualBasinGeometry

/-! # Actual stable-basin limits from deterministic geometric sources

The prefix gap is produced by the finite pressure/filtration pipeline. This
consumer derives every live-orbit and heteroclinic control premise from ordinary
stable/unstable approach and strict trapping, then applies the actual exp(phi)
kernel. Strict trapping is an explicit additional gate for the global statement.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedStableBasin
open AbsorbingMarkovChains ComplexStrongFeller LayerOperators RestrictedLayerChain
open LayerQuasiErgodic AmbientPrefixEigenfunction PrefixCorrespondence
open LeanShared.ControlledPlaqueClosure HeteroclinicAccessibility ActualBasinGeometry
variable {X Ω I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (C : CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U) [CompactSpace U]

theorem full_conditioned_limit_of_actual_selected_stable_basin
    (hprefix : ∀ x ∈ U, C.killedTransition x Uᶜ = 0)
    (dg : RankOneSpectralData (transferOperator (𝕜 := ℝ) (chain C U hU)
      (strongFeller C hSF U hU)) (1 : U →ᵇ ℝ))
    (Λ : Set U) (hΛpos : ∀ y ∈ Λ, 0 < dg.eigenvector y)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] [ρ.IsOpenPosMeasure]
    (F : X × Ω → X) (hF : Measurable F) (hFc : Continuous F)
    (V : Set X) (hV : MeasurableSet V) (O : Set X) (hO : IsOpen O) (hOV : O ⊆ V) (φ : X → ℝ) (hφ : Measurable φ)
    (W : ℝ) (hW : 0 < W) (hbound : ∀ x, Real.exp (φ x) ≤ W)
    (hmodel : C.killedTransition = (NoiseKernel.chain ρ F hF V hV
      (fun x => Real.exp (φ x)) (Real.measurable_exp.comp hφ) W hW hbound).killedTransition)
    (T : X ≃ₜ X) (A : Set X) (hstrict : MapsTo T (closure A) A)
    (hUadapt : MapsTo T U (interior U)) (hOactual : O = interior Aᶜ)
    (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (Γ : I → Set X) (hΓV : ∀ i, Γ i ⊆ U ∩ O)
    (hT : ∀ i, MapsTo T (Γ i) (Γ i)) (hinv : ∀ i, MapsTo T.symm (Γ i) (Γ i))
    (htrans : ∀ i, forwardTransitiveOn T (Γ i))
    (hcompact : ∀ i, IsCompact (Γ i))
    (hinside : ∀ i, Γ i ⊆ interior U)
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U ∩ O, ∀ y ∈ U ∩ O, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (edge : I → I → Prop)
    (hedge : ∀ i j, edge i j → ∃ z : X,
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ j,
        dist ((T : X → X)^[n + 1] z) y < r) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ i,
        dist ((T.symm : X → X)^[n] z) y < r))
    {i root : I} (hreach : Relation.ReflTransGen edge i root)
    (hroot : Γ root = Subtype.val '' Λ) (x : U)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ i,
      dist ((T : X → X)^[n + 1] x.val) y < r)
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) :
    Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
      (𝓝 (∫ y, f y ∂(productMeasure (chain C U hU) (strongFeller C hSF U hU) dg).map Subtype.val)) := by
  have hΓA : ∀ j, Γ j ⊆ interior Aᶜ := by
    intro j y hy
    rw [← hOactual]
    exact (hΓV j hy).2
  have hedgelive : ∀ j l, edge j l → HeteroclinicWitness T (U ∩ O) (Γ j) (Γ l) := by
    intro j l hjl
    let z := Classical.choose (hedge j l hjl)
    have hzfuture := (Classical.choose_spec (hedge j l hjl)).1
    have hzpast := (Classical.choose_spec (hedge j l hjl)).2
    rw [hOactual]
    exact actual_heteroclinic_witness T A U (Γ j) (Γ l) hstrict hUadapt
      (hinside j) (hΓA l) (hcompact j) (hcompact l)
      (hT j) (hinv j) (hT l) (hinv l) z hzfuture hzpast
  have happ : LeanShared.AbsorbingBasinSeparation.Approaches T (Γ i) x.val :=
    approaches_of_metric T (Γ i) (hcompact i) x.val (by
      intro r hr
      obtain ⟨n, y, hy, hd⟩ := happroach r hr
      exact ⟨n + 1, y, hy, hd⟩)
  have hlive : ∀ n : ℕ, (T : X → X)^[n] x.val ∈ U ∩ O := by
    rw [hOactual]
    exact stable_orbit_in_selected_live_prefix T A U (Γ i) hstrict hUadapt
      (hΓA i) (hT i) x.val x.property happ
  exact SelectedGlobalBasin.full_conditioned_limit_of_internal_selected_stable_basin
    C hSF U hU hprefix dg Λ hΛpos ρ F hF hFc V hV O hO hOV φ hφ W hW hbound
    hmodel T ω₀ hzero Γ hΓV hT hinv htrans hδ himage edge hedgelive hreach hroot
    x hlive happroach f hf hb

end ConditionedStochasticStabilityHyperbolic.Global.ActualSelectedStableBasin
