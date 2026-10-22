module

public import ConditionedStochasticStabilityHyperbolic.Global.SelectedPrefixPackage
public import ConditionedStochasticStabilityHyperbolic.Global.AmbientPrefixEigenfunction
public import ConditionedStochasticStabilityHyperbolic.Global.HeteroclinicAccessibility

/-! # Full actual-process limits for an internally selected pressure root

The selected root may lie strictly inside the prefix. Its prefix leading data
is constructed by the two-sided layer argument; actual exp(real phi) kernel
positivity along stable and heteroclinic controls derives starting-state
positivity and transfers the actual finite conditioned process to the prefix.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.Global.SelectedGlobalBasin
open AbsorbingMarkovChains ComplexStrongFeller LayerOperators RestrictedLayerChain
open LayerQuasiErgodic AmbientPrefixEigenfunction PrefixCorrespondence
open LeanShared.ControlledPlaqueClosure HeteroclinicAccessibility
variable {X Ω I : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Ω] [MeasurableSpace Ω]
  (C : CanonicalChain X) (hSF : HasStrongFellerKernel C)
  (U : Set X) (hU : MeasurableSet U) [CompactSpace U]

/-- The actual selected-prefix measure governs full-process conditioned
statistics for each stable basin with graph access to its selected root. -/
theorem full_conditioned_limit_of_internal_selected_stable_basin
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
    (T : X ≃ₜ X) (ω₀ : Ω) (hzero : ∀ x, F (x, ω₀) = T x)
    (Γ : I → Set X) (hΓV : ∀ i, Γ i ⊆ U ∩ O)
    (hT : ∀ i, MapsTo T (Γ i) (Γ i)) (hinv : ∀ i, MapsTo T.symm (Γ i) (Γ i))
    (htrans : ∀ i, forwardTransitiveOn T (Γ i))
    {δ : ℝ} (hδ : 0 < δ)
    (himage : ∀ z ∈ U ∩ O, ∀ y ∈ U ∩ O, dist (T z) y < δ → ∃ ω, F (z, ω) = y)
    (edge : I → I → Prop)
    (hedge : ∀ i j, edge i j → HeteroclinicWitness T (U ∩ O) (Γ i) (Γ j))
    {i root : I} (hreach : Relation.ReflTransGen edge i root)
    (hroot : Γ root = Subtype.val '' Λ) (x : U)
    (hlive : ∀ n : ℕ, (T : X → X)^[n] x.val ∈ U ∩ O)
    (happroach : ∀ r : ℝ, 0 < r → ∃ n : ℕ, ∃ y ∈ Γ i,
      dist ((T : X → X)^[n + 1] x.val) y < r)
    (f : X → ℝ) (hf : Measurable f) (hb : ∃ B : ℝ, ∀ y, ‖f y‖ ≤ B) :
    Tendsto (MeasurableCanonical.pathAverage C f x.val) atTop
      (𝓝 (∫ y, f y ∂(productMeasure (chain C U hU) (strongFeller C hSF U hU) dg).map Subtype.val)) := by
  let g := ambientVector C hSF U hU dg
  have hrootpos : ∀ y ∈ Γ root, 0 < g y := by
    intro y hy
    rw [hroot] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [ambientVector_coe C hSF U hU dg p]
    exact hΛpos p hp
  have hstep : ∀ z ∈ U ∩ O, ∀ ω, F (z, ω) ∈ U ∩ O → 0 < g (F (z, ω)) → 0 < g z := by
    intro z hz ω hy hp
    exact positive_before_control_on_prefix C hSF U hU dg ρ F hF hFc V hV O hO hOV φ hφ W hW hbound
      hprefix hmodel z hz.1 ω hy.2 hp
  have hpos := positive_along_graph_reachability T F ω₀ hzero (U ∩ O) Γ hΓV hT hinv htrans
    g g.continuous hstep hδ himage edge hedge hreach hrootpos
  obtain ⟨n, y, hy, hnear⟩ := happroach δ hδ
  have hnear' : dist (T ((T : X → X)^[n] x.val)) y < δ := by
    simpa only [Function.iterate_succ_apply'] using hnear
  obtain ⟨ω, hω⟩ := himage _ (hlive n) y (hΓV i hy) hnear'
  have hn : 0 < g ((T : X → X)^[n] x.val) := by
    apply hstep _ (hlive n) ω
    · rw [hω]; exact hΓV i hy
    · rw [hω]; exact hpos y hy
  have hback : ∀ m : ℕ, ∀ z : X,
      (∀ j, j ≤ m → (T : X → X)^[j] z ∈ U ∩ O) →
      0 < g ((T : X → X)^[m] z) → 0 < g z := by
    intro m
    induction m with
    | zero => intro z _ hp; exact hp
    | succ m ih =>
      intro z hz hp
      apply hstep z (hz 0 (Nat.zero_le _)) ω₀
      · rw [hzero]; exact hz 1 (Nat.succ_le_succ (Nat.zero_le m))
      · rw [hzero]
        apply ih (T z)
        · intro j hj
          rw [← Function.iterate_succ_apply]
          exact hz (j + 1) (Nat.succ_le_succ hj)
        · simpa only [Function.iterate_succ_apply] using hp
  have hx : 0 < dg.eigenvector x := by
    rw [← ambientVector_coe C hSF U hU dg x]
    exact hback n x.val (fun j _ => hlive j) hn
  exact full_process_limit_from_prefix C U hU hprefix (strongFeller C hSF U hU) dg f hf hb x hx

end ConditionedStochasticStabilityHyperbolic.Global.SelectedGlobalBasin
