module

public import LeanShared.Probability.KernelTrajectorySupport
public import LeanShared.Dynamics.TransientNeighborhood
public import ConditionedStochasticStabilityHyperbolic.Restriction.Transient
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseKernel
public import AbsorbingMarkovChains.PathSurvival
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Actual noise-layer paths have finite extinction

Transition support is transferred from the original pushforward noise law to
the actual canonical path law. No measurable selection of noise parameters
is assumed. This proves nilpotence only for the chain killed on entering the
core neighborhood or exiting the compact region. It does not split the full
continuous operator into bounded triangular coordinates.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

open AbsorbingMarkovChains LeanShared.RandomMapKernel LeanShared.WeightedConditioning

section Relations

variable {X : Type*} [MeasurableSpace X]

/-- Live/live pairs violating a measurable transition relation. -/
def badLivePairs (R : X × X → Prop) : Set (Option X × Option X) :=
  Prod.map Option.some Option.some '' {p | ¬R p}

theorem badLivePairs_measurable {R : X × X → Prop} (hR : MeasurableSet {p | R p}) :
    MeasurableSet (badLivePairs R) :=
  (measurableEmbedding_some_state.prodMap measurableEmbedding_some_state).measurableSet_image'
    hR.compl

omit [MeasurableSpace X] in
theorem not_mem_badLivePairs_some {R : X × X → Prop} (x y : X) :
    (some x, some y) ∉ badLivePairs R ↔ R (x, y) := by
  simp [badLivePairs, Set.mem_image, Prod.exists, Prod.map]

omit [MeasurableSpace X] in
theorem not_mem_badLivePairs_none_left (R : X × X → Prop) (y : Option X) :
    (none, y) ∉ badLivePairs R := by
  rintro ⟨⟨x, z⟩, _hbad, heq⟩
  have hf : some x = (none : Option X) := congrArg (fun p : Option X × Option X => p.1) heq
  cases hf

/-- A measurable support relation for the killed kernel holds at every live
pair of consecutive canonical observations, almost surely. -/
theorem ae_live_transition_relation (C : CanonicalChain X)
    (R : X × X → Prop) (hR : MeasurableSet {p | R p})
    (hsupport : ∀ u, ∀ᵐ v ∂C.killedTransition u, R (u, v)) (x : X) (n : ℕ) :
    ∀ᵐ ω ∂C.pathMeasure x, ∀ u v,
      ω n = some u → ω (n + 1) = some v → R (u, v) := by
  let Q : (((i : Finset.Iic n) → Option X) × Option X) → Prop :=
    fun p => (p.1 ⟨n, by simp⟩, p.2) ∉ badLivePairs R
  have hQ : MeasurableSet {p | Q p} :=
    (badLivePairs_measurable hR).compl.preimage
      (((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd)
  have hk : ∀ h, ∀ᵐ v ∂C.historyKernel n h, Q (h, v) := by
    intro h
    change ∀ᵐ v ∂C.transition (h ⟨n, by simp⟩), (h ⟨n, by simp⟩, v) ∉ badLivePairs R
    cases he : h ⟨n, by simp⟩ with
    | none => exact ae_of_all _ (not_mem_badLivePairs_none_left R)
    | some u =>
      have hs : MeasurableSet {v | ¬R (u, v)} := hR.compl.preimage measurable_prodMk_left
      have hzero : C.transition (some u) (Option.some '' {v | ¬R (u, v)}) = 0 := by
        rw [← C.killedTransition_apply u _ hs]
        exact ae_iff.mp (hsupport u)
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hzero] with v hv
      cases v with
      | none =>
          rintro ⟨⟨a, b⟩, _hbad, heq⟩
          have hf : some b = (none : Option X) :=
            congrArg (fun p : Option X × Option X => p.2) heq
          cases hf
      | some v =>
          apply (not_mem_badLivePairs_some u v).2
          by_contra hbad
          exact hv ⟨v, hbad, rfl⟩
  have hp := LeanShared.KernelTrajectorySupport.ae_relation_of_joint_law
    (C.pathMeasure x) (C.historyKernel n) (Preorder.frestrictLe n)
    (fun ω => ω (n + 1)) (Preorder.measurable_frestrictLe n)
    (measurable_pi_apply (n + 1)) (C.pathMeasure_past_next x n).symm Q hQ hk
  filter_upwards [hp] with ω hω
  intro u v hu hv
  change (ω n, ω (n + 1)) ∉ badLivePairs R at hω
  rw [hu, hv] at hω
  exact (not_mem_badLivePairs_some u v).1 hω

end Relations

section NoiseSupport

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Every live destination of the weighted noise chain satisfies each
measurable relation satisfied by its surviving random-map images. -/
theorem noise_chain_support (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F) (L : Set X) (hL : MeasurableSet L)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    (R : X × X → Prop) (hR : MeasurableSet {p | R p})
    (himages : ∀ x ω, F (x, ω) ∈ L → R (x, F (x, ω))) :
    ∀ x, ∀ᵐ y ∂(NoiseKernel.chain ρ F hF L hL w hw W hW hwW).killedTransition x,
      R (x, y) := by
  intro x
  apply ae_iff.mpr
  have hs : MeasurableSet {y | ¬R (x, y)} := hR.compl.preimage measurable_prodMk_left
  rw [NoiseKernel.chain, WeightedKernel.ofBoundedWeight_killedTransition]
  change (ENNReal.ofReal (w x / W) • ((ρ.map (fun ω => F (x, ω))).restrict L))
    {y | ¬R (x, y)} = 0
  rw [Measure.smul_apply, Measure.restrict_apply hs,
    Measure.map_apply (f := fun ω => F (x, ω))
      (hF.comp measurable_prodMk_left) (hs.inter hL)]
  have hempty : (fun ω => F (x, ω)) ⁻¹' ({y | ¬R (x, y)} ∩ L) = ∅ := by
    ext ω
    constructor
    · intro hbad
      exact (hbad.1 (himages x ω hbad.2)).elim
    · intro hbad
      exact hbad.elim
  rw [hempty, measure_empty, smul_eq_mul, mul_zero]

end NoiseSupport

section FiniteExtinction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Almost-sure live-step containment and closeness force finite extinction in the actual layer
chain. One extra step accommodates ambient initial states outside the layer, since the noise
adapter retains the ambient type. -/
theorem layer_extinction_of_live_relation
    (C : CanonicalChain X) (T : X → X) (L : Set X) (N : ℕ) (δ : ℝ)
    (hrel : MeasurableSet {p : X × X | p.2 ∈ L ∧
      (p.1 ∈ L → dist p.2 (T p.1) < δ)})
    (hsupport : ∀ u, ∀ᵐ v ∂C.killedTransition u,
      v ∈ L ∧ (u ∈ L → dist v (T u) < δ))
    (hexit : ∀ z : ℕ → X, z 0 ∈ L →
      (∀ j < N, z j ∈ L → dist (z (j + 1)) (T (z j)) < δ) →
      ∃ j ≤ N, z j ∉ L) :
    ∀ x, C.pathMeasure x (CanonicalChain.survival (N + 1)) = 0 := by
  intro x
  have hsteps : ∀ᵐ ω ∂C.pathMeasure x, ∀ n, ∀ u v,
      ω n = some u → ω (n + 1) = some v →
        v ∈ L ∧ (u ∈ L → dist v (T u) < δ) := by
    exact ae_all_iff.2 (fun n => ae_live_transition_relation C _ hrel hsupport x n)
  have hn : ∀ᵐ ω ∂C.pathMeasure x, ω ∉ CanonicalChain.survival (N + 1) := by
    filter_upwards [hsteps] with ω hω
    intro hs
    let z : ℕ → X := fun j => (ω (j + 1)).getD x
    have hsome (j : ℕ) (hj : j ≤ N + 1) : ω j = some ((ω j).getD x) := by
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hs j hj)
      simp [hy]
    have hz0 : z 0 ∈ L :=
      (hω 0 ((ω 0).getD x) (z 0) (hsome 0 (by omega)) (hsome 1 (by omega))).1
    have hstep : ∀ j < N, z j ∈ L → dist (z (j + 1)) (T (z j)) < δ := by
      intro j hj hzj
      apply (hω (j + 1) (z j) (z (j + 1))
        (hsome (j + 1) (by omega)) (hsome (j + 1 + 1) (by omega))).2 hzj
    obtain ⟨j, hj, hbad⟩ := hexit z hz0 hstep
    have hinside : z j ∈ L :=
      (hω j ((ω j).getD x) (z j) (hsome j (by omega)) (hsome (j + 1) (by omega))).1
    exact hbad hinside
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hn

end FiniteExtinction

section GeometricNoise

variable {X Ω : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Ω]

/-- Uniform geometric entrance-or-exit is connected to the actual weighted noise chain killed on the
complement `K \ U`. -/
theorem noise_layer_extinction_of_exit
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (N : ℕ) (δ : ℝ)
    (hexit : ∀ z : ℕ → X, z 0 ∈ K \ U →
      (∀ j < N, z j ∈ K \ U → dist (z (j + 1)) (T (z j)) < δ) →
      ∃ j ≤ N, z j ∉ K ∨ z j ∈ U)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    (hclose : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) :
    ∀ x, (NoiseKernel.chain ρ F hF (K \ U) (hK.isClosed.measurableSet.diff hU.measurableSet)
      w hw W hW hwW).pathMeasure x (CanonicalChain.survival (N + 1)) = 0 := by
  let L := K \ U
  have hL : MeasurableSet L := hK.isClosed.measurableSet.diff hU.measurableSet
  let R : X × X → Prop := fun p => p.2 ∈ L ∧ (p.1 ∈ L → dist p.2 (T p.1) < δ)
  have hR : MeasurableSet {p | R p} := by
    apply MeasurableSet.inter
    · exact hL.preimage measurable_snd
    · apply MeasurableSet.imp
      · exact hL.preimage measurable_fst
      · exact measurableSet_lt (measurable_snd.dist (T.continuous.measurable.comp measurable_fst))
          measurable_const
  have hsupport := noise_chain_support ρ F hF L hL w hw W hW hwW R hR
    (fun x ω hy => ⟨hy, fun hx => hclose x hx.1 ω⟩)
  apply layer_extinction_of_live_relation _ T L N δ hR hsupport
  intro z hz hstep
  obtain ⟨j, hj, hbad⟩ := hexit z hz hstep
  exact ⟨j, hj, by simpa only [L, Set.mem_sdiff, not_and_or, not_not] using hbad⟩

/-- The geometric assumptions produce a common horizon and map tolerance
for actual killed noise-layer processes. -/
theorem exists_pos_noise_layer_extinction [CompactSpace X]
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : X × Ω → X) (hF : Measurable F),
        (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) →
        ∀ x, (NoiseKernel.chain ρ F hF (K \ U)
          (hK.isClosed.measurableSet.diff hU.measurableSet) w hw W hW hwW).pathMeasure x
            (CanonicalChain.survival (N + 1)) = 0 := by
  obtain ⟨N, hN, δ, hδ, hexit⟩ := LeanShared.exists_pos_robust_entrance_or_exit T
    (CompactSpace.uniformContinuous_of_continuous T.continuous) hK hU hcore
  exact ⟨N, hN, δ, hδ, fun F hF hclose =>
    noise_layer_extinction_of_exit T K U hK hU N δ hexit ρ F hF w hw W hW hwW hclose⟩

/-- The manuscript's uniform noise bound supplies an actual uniform finite
extinction horizon for its weighted complement chain. -/
theorem exists_small_noise_layer_extinction [CompactSpace X]
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (hcore : LeanShared.isolatedCore T K ⊆ U)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : ℝ → X × Ω → X) (hF : ∀ ε, Measurable (F ε))
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    {C : ℝ} (hC : 0 ≤ C)
    (hnoise : ∀ ε > 0, ∀ x ∈ K, ∀ ω, dist (F ε (x, ω)) (T x) ≤ C * ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε, 0 < ε → ε < ε₀ → ∀ x,
        (NoiseKernel.chain ρ (F ε) (hF ε) (K \ U)
          (hK.isClosed.measurableSet.diff hU.measurableSet) w hw W hW hwW).pathMeasure x
            (CanonicalChain.survival (N + 1)) = 0 := by
  obtain ⟨N, hN, δ, hδ, hexit⟩ := exists_pos_noise_layer_extinction T K U hK hU hcore
    ρ w hw W hW hwW
  have hC1 : 0 < C + 1 := by linarith
  refine ⟨N, hN, δ / (C + 1), div_pos hδ hC1, ?_⟩
  intro ε hε hsmall
  apply hexit (F ε) (hF ε)
  intro x hx ω
  have hprod : ε * (C + 1) < δ := (lt_div_iff₀ hC1).mp hsmall
  have hbound := hnoise ε hε x hx ω
  nlinarith

/-- Any real or complex bounded continuous operator representing this actual
killed layer is nilpotent at the proven finite horizon. -/
theorem noise_layer_nilpotent_of_exit
    (T : X ≃ₜ X) (K U : Set X) (hK : IsCompact K) (hU : IsOpen U)
    (N : ℕ) (δ : ℝ)
    (hexit : ∀ z : ℕ → X, z 0 ∈ K \ U →
      (∀ j < N, z j ∈ K \ U → dist (z (j + 1)) (T (z j)) < δ) →
      ∃ j ≤ N, z j ∉ K ∨ z j ∈ U)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (F : X × Ω → X) (hF : Measurable F)
    (w : X → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    (hclose : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ)
    {𝕜 : Type*} [RCLike 𝕜] (D : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
    (hD : ∀ (f : X →ᵇ 𝕜) (x : X), (D f) x =
      ∫ y, f y ∂(NoiseKernel.chain ρ F hF (K \ U)
        (hK.isClosed.measurableSet.diff hU.measurableSet) w hw W hW hwW).killedTransition x) :
    D ^ (N + 1) = 0 :=
  nilpotent_of_uniform_finite_extinction _ D hD (N + 1)
    (noise_layer_extinction_of_exit T K U hK hU N δ hexit ρ F hF w hw W hW hwW hclose)

end GeometricNoise

end ConditionedStochasticStabilityHyperbolic.Restriction
