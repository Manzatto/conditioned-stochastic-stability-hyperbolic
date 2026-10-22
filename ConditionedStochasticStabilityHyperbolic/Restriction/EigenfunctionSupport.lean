module

public import LeanShared.Analysis.SpectralVanishing
public import ConditionedStochasticStabilityHyperbolic.Restriction.NoiseTransient

/-!
# Pointwise spectral vanishing from actual finite survival extinction

An extinct starting state annihilates every bounded continuous observation
after that finite horizon. Therefore all nonzero-eigenvalue generalized
eigenfunctions vanish there. This argument is local to evaluation and does
not assert nilpotence of the full operator or a bounded spatial splitting.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

open AbsorbingMarkovChains AbsorbingMarkovChains.FeynmanKac

section Functional

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {𝕜 : Type*} [RCLike 𝕜]
  (C : CanonicalChain X) (P : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (hP : ∀ (f : X →ᵇ 𝕜) (x : X), (P f) x = ∫ y, f y ∂C.killedTransition x)

include hP

/-- Zero survival at one starting state annihilates its evaluation of every
`N`-step transferred bounded continuous function. -/
theorem kernel_power_eval_zero_of_survival_zero (x : X) (N : ℕ)
    (hs : C.pathMeasure x (CanonicalChain.survival N) = 0) :
    (BoundedContinuousFunction.evalCLM 𝕜 x).comp (P ^ N) = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  change ((P ^ N) f) x = 0
  have hk := integral_prod_eq_killedWord C (fun _ _ => (1 : 𝕜))
    (fun _ => measurable_const) zero_le_one (fun _ _ => by simp) N
    f.continuous.measurable (norm_nonneg f) f.norm_coe_le_norm x
  have hn : ∀ᵐ ω ∂C.pathMeasure x, ω ∉ CanonicalChain.survival N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hs
  have hz : (fun ω => (∏ i ∈ range N, ext (fun _ : X => (1 : 𝕜)) (ω i)) *
      ext (f : X → 𝕜) (ω N)) =ᵐ[C.pathMeasure x] 0 := by
    filter_upwards [hn, C.ae_mem_survival_iff x N] with ω hnot hsurv
    have hnone : ω N = none := by
      by_contra h
      exact hnot (hsurv.2 h)
    simp [hnone]
  rw [integral_congr_ae hz] at hk
  change (∫ _ω, (0 : 𝕜) ∂C.pathMeasure x) = _ at hk
  rw [integral_zero, killedWord_one_eq_power C P hP N f] at hk
  exact hk.symm

/-- Complex generalized eigenfunctions vanish at every finitely extinct
starting state, with the nonzero-eigenvalue condition explicit. -/
theorem generalized_eigenfunction_vanishes_of_finite_extinction
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜)
    (hgen : ((P - z • 1) ^ k) f = 0) (x : X) (N : ℕ)
    (hs : C.pathMeasure x (CanonicalChain.survival N) = 0) : f x = 0 :=
  LeanShared.SpectralVanishing.eval_generalized_eq_zero P
    (BoundedContinuousFunction.evalCLM 𝕜 x) hz N k
    (kernel_power_eval_zero_of_survival_zero C P hP x N hs) f hgen

theorem eigenfunction_vanishes_of_finite_extinction
    {z : 𝕜} (hz : z ≠ 0) (f : X →ᵇ 𝕜) (heig : P f = z • f) (x : X) (N : ℕ)
    (hs : C.pathMeasure x (CanonicalChain.survival N) = 0) : f x = 0 :=
  LeanShared.SpectralVanishing.eval_eigenvector_eq_zero P
    (BoundedContinuousFunction.evalCLM 𝕜 x) hz N
    (kernel_power_eval_zero_of_survival_zero C P hP x N hs) f heig

/-- Nonzero values of generalized eigenfunctions have positive survival at
every finite horizon. -/
theorem generalized_eigenfunction_nonzero_survives
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜)
    (hgen : ((P - z • 1) ^ k) f = 0) (x : X) (hx : f x ≠ 0) (N : ℕ) :
    C.pathMeasure x (CanonicalChain.survival N) ≠ 0 := by
  intro hs
  exact hx (generalized_eigenfunction_vanishes_of_finite_extinction C P hP hz k f hgen x N hs)

/-- The function support is contained in the actual nonescaping state set.
No positivity, irreducibility, or simplicity of the eigenvalue is required. -/
theorem generalized_eigenfunction_support_subset_surviving
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜)
    (hgen : ((P - z • 1) ^ k) f = 0) :
    Function.support (f : X → 𝕜) ⊆ StandingHypothesis.survivingSet C.killedTransition := by
  intro x hx hescape
  obtain ⟨N, _hN, hs⟩ := hescape
  apply hx
  apply generalized_eigenfunction_vanishes_of_finite_extinction C P hP hz k f hgen x N
  rw [C.pathMeasure_survival]
  exact hs

/-- Uniform or point-dependent finite exit bounds on a bad region give the
support vanishing needed before restriction, without global block coordinates. -/
theorem generalized_eigenfunction_vanishes_on_region
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜)
    (hgen : ((P - z • 1) ^ k) f = 0) (B : Set X)
    (hext : ∀ x ∈ B, ∃ N : ℕ, C.pathMeasure x (CanonicalChain.survival N) = 0) :
    ∀ x ∈ B, f x = 0 := by
  intro x hx
  obtain ⟨N, hs⟩ := hext x hx
  exact generalized_eigenfunction_vanishes_of_finite_extinction C P hP hz k f hgen x N hs

end Functional

section NoiseExit

variable {Y Ω : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace Ω]

/-- The actual path's zeroth coordinate is its specified starting state. -/
theorem ae_path_initial_state (D : CanonicalChain Y) (x : Y) :
    ∀ᵐ ω ∂D.pathMeasure x, ω 0 = some x := by
  have hs : MeasurableSet ({some x} : Set (Option Y)) := by
    simpa only [image_singleton] using
      measurableEmbedding_some_state.measurableSet_image' (measurableSet_singleton x)
  have hinit : ∀ᵐ z ∂(D.pathMeasure x).map (fun ω => ω 0), z = some x := by
    rw [D.pathMeasure_initial]
    exact (ae_dirac_iff hs).2 rfl
  exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable hinit

/-- Pointwise bad-region exit uses the genuine initial law. It does not
force extinction at starting states that lie outside the bad region. -/
theorem finite_extinction_from_region_relation
    (D : CanonicalChain Y) (T : Y → Y) (K B : Set Y) (hBK : B ⊆ K) (N : ℕ) (δ : ℝ)
    (hrel : MeasurableSet {p : Y × Y | p.2 ∈ K ∧
      (p.1 ∈ K → dist p.2 (T p.1) < δ)})
    (hsupport : ∀ u, ∀ᵐ v ∂D.killedTransition u,
      v ∈ K ∧ (u ∈ K → dist v (T u) < δ))
    (hexit : ∀ z : ℕ → Y, z 0 ∈ B →
      (∀ j < N, z j ∈ K → dist (z (j + 1)) (T (z j)) < δ) →
      ∃ j ≤ N, z j ∉ K) :
    ∀ x ∈ B, D.pathMeasure x (CanonicalChain.survival N) = 0 := by
  intro x hx
  have hsteps : ∀ᵐ ω ∂D.pathMeasure x, ∀ n, ∀ u v,
      ω n = some u → ω (n + 1) = some v →
        v ∈ K ∧ (u ∈ K → dist v (T u) < δ) :=
    ae_all_iff.2 (fun n => ae_live_transition_relation D _ hrel hsupport x n)
  have hn : ∀ᵐ ω ∂D.pathMeasure x, ω ∉ CanonicalChain.survival N := by
    filter_upwards [hsteps, ae_path_initial_state D x] with ω hω hinit
    intro hs
    let z : ℕ → Y := fun j => (ω j).getD x
    have hsome (j : ℕ) (hj : j ≤ N) : ω j = some (z j) := by
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp (hs j hj)
      simp [z, hy]
    have hz0 : z 0 = x := by simp [z, hinit]
    have hinside (j : ℕ) (hj : j ≤ N) : z j ∈ K := by
      cases j with
      | zero => rw [hz0]; exact hBK hx
      | succ j => exact (hω j (z j) (z (j + 1)) (hsome j (by omega)) (hsome (j + 1) hj)).1
    have hstep : ∀ j < N, z j ∈ K → dist (z (j + 1)) (T (z j)) < δ := by
      intro j hj hzj
      exact (hω j (z j) (z (j + 1)) (hsome j (by omega)) (hsome (j + 1) (by omega))).2 hzj
    obtain ⟨j, hj, hbad⟩ := hexit z (hz0.symm ▸ hx) hstep
    exact hbad (hinside j hj)
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hn

variable [SecondCountableTopology Y]

/-- Robust exit from a bad subset of the live region gives actual finite
extinction for the weighted noise chain killed on exiting `K`. -/
theorem noise_region_extinction_of_exit
    (T : Y ≃ₜ Y) (K B : Set Y) (hK : MeasurableSet K) (hBK : B ⊆ K)
    (N : ℕ) (δ : ℝ)
    (hexit : ∀ z : ℕ → Y, z 0 ∈ B →
      (∀ j < N, z j ∈ K → dist (z (j + 1)) (T (z j)) < δ) → ∃ j ≤ N, z j ∉ K)
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : Y × Ω → Y) (hF : Measurable F)
    (w : Y → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W)
    (hclose : ∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) :
    ∀ x ∈ B, (NoiseKernel.chain ρ F hF K hK w hw W hW hwW).pathMeasure x
      (CanonicalChain.survival N) = 0 := by
  let R : Y × Y → Prop := fun p => p.2 ∈ K ∧ (p.1 ∈ K → dist p.2 (T p.1) < δ)
  have hR : MeasurableSet {p | R p} :=
    (hK.preimage measurable_snd).inter
      (MeasurableSet.imp (hK.preimage measurable_fst)
        (measurableSet_lt (measurable_snd.dist (T.continuous.measurable.comp measurable_fst))
          measurable_const))
  have hs := noise_chain_support ρ F hF K hK w hw W hW hwW R hR
    (fun x ω hy => ⟨hy, fun hx => hclose x hx ω⟩)
  exact finite_extinction_from_region_relation _ T K B hBK N δ hR hs hexit

/-- Compact bad regions disjoint from the deterministic forward trapped set
produce a uniform horizon/tolerance for actual noise survival extinction. -/
theorem exists_pos_noise_region_extinction [CompactSpace Y]
    (T : Y ≃ₜ Y) (K B : Set Y) (hK : IsClosed K) (hB : IsCompact B) (hBK : B ⊆ K)
    (hdis : Disjoint B (LeanShared.forwardTrapped T K))
    (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (w : Y → ℝ) (hw : Measurable w) (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) :
    ∃ N : ℕ, 0 < N ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Y × Ω → Y) (hF : Measurable F),
        (∀ x ∈ K, ∀ ω, dist (F (x, ω)) (T x) < δ) → ∀ x ∈ B,
        (NoiseKernel.chain ρ F hF K hK.measurableSet w hw W hW hwW).pathMeasure x
          (CanonicalChain.survival N) = 0 := by
  obtain ⟨N, hN, δ, hδ, hexit⟩ := LeanShared.exists_pos_robust_forward_exit
    (CompactSpace.uniformContinuous_of_continuous T.continuous) hK hB hdis
  exact ⟨N, hN, δ, hδ, fun F hF hclose => noise_region_extinction_of_exit
    T K B hK.measurableSet hBK N δ hexit ρ F hF w hw W hW hwW hclose⟩

end NoiseExit

end ConditionedStochasticStabilityHyperbolic.Restriction
