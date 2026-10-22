module

public import LeanShared.Analysis.TransientRestriction
public import LeanShared.Dynamics.RobustFiniteIsolation
public import AbsorbingMarkovChains.FeynmanKac

/-!
# From finite extinction in an actual layer chain to nilpotence

The chain in this module must be the killed *layer* chain. Its finite-horizon
extinction is an explicit input, and the bounded operator must represent that
chain. This does not assert nilpotence of the whole exterior operator or that
an indicator of a Borel layer preserves continuous functions.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

open AbsorbingMarkovChains AbsorbingMarkovChains.FeynmanKac

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {𝕜 : Type*} [RCLike 𝕜]
  (C : CanonicalChain X) (D : (X →ᵇ 𝕜) →L[𝕜] (X →ᵇ 𝕜))
  (hD : ∀ (f : X →ᵇ 𝕜) (x : X), (D f) x = ∫ y, f y ∂C.killedTransition x)

include hD

omit [OpensMeasurableSpace X] in
/-- The transfer word with no observations is exactly the operator power. -/
theorem killedWord_one_eq_power (n : ℕ) (f : X →ᵇ 𝕜) :
    killedWord C (fun _ _ => (1 : 𝕜)) n (f : X → 𝕜) = ⇑((D ^ n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [killedWord]
      have heq : (fun y => (1 : 𝕜) * ∫ z, f z ∂C.killedTransition y) =
          (D f : X → 𝕜) := by
        funext y
        rw [one_mul, ← hD]
      rw [heq, ih, pow_succ, mul_apply_eq_comp]

/-- A common finite survival horizon with zero mass forces nilpotence of the
represented continuous operator, over either real or complex scalars. -/
theorem nilpotent_of_uniform_finite_extinction (N : ℕ)
    (hext : ∀ x, C.pathMeasure x (CanonicalChain.survival N) = 0) : D ^ N = 0 := by
  apply ContinuousLinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro x
  have hk := integral_prod_eq_killedWord C (fun _ _ => (1 : 𝕜))
    (fun _ => measurable_const) zero_le_one (fun _ _ => by simp) N
    f.continuous.measurable (norm_nonneg f) f.norm_coe_le_norm x
  have hn : ∀ᵐ ω ∂C.pathMeasure x, ω ∉ CanonicalChain.survival N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hext x
  have hz : (fun ω => (∏ i ∈ range N, ext (fun _ : X => (1 : 𝕜)) (ω i)) *
      ext (f : X → 𝕜) (ω N)) =ᵐ[C.pathMeasure x] 0 := by
    filter_upwards [hn, C.ae_mem_survival_iff x N] with ω hnot hsurv
    have hnone : ω N = none := by
      by_contra hnone
      exact hnot (hsurv.2 hnone)
    simp [hnone]
  rw [integral_congr_ae hz] at hk
  change (∫ _ω, (0 : 𝕜) ∂C.pathMeasure x) = _ at hk
  rw [integral_zero, killedWord_one_eq_power C D hD N f] at hk
  exact hk.symm

/-- A geometric exit-by-`N` certificate transfers to nilpotence once the
actual layer paths are almost surely killed by that horizon. -/
theorem nilpotent_of_ae_exit_by (N : ℕ)
    (hexit : ∀ x, ∀ᵐ ω ∂C.pathMeasure x, ∃ i ≤ N, ω i = none) : D ^ N = 0 := by
  apply nilpotent_of_uniform_finite_extinction C D hD N
  intro x
  have hn : ∀ᵐ ω ∂C.pathMeasure x, ω ∉ CanonicalChain.survival N := by
    filter_upwards [hexit x] with ω hω
    obtain ⟨i, hi, hnone⟩ := hω
    intro hs
    exact (hs i hi) hnone
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hn

/-- The paper's restriction/lifting algebra, with nilpotence supplied by
actual finite extinction of the represented complement layer. The first
coordinate is the retained region, and the layer is a separate state space. -/
def generalizedLayerRestrictionEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E →L[𝕜] E) (B : E →L[𝕜] (X →ᵇ 𝕜))
    {z : 𝕜} (hz : z ≠ 0) (N : ℕ)
    (hext : ∀ x, C.pathMeasure x (CanonicalChain.survival N) = 0) (k : ℕ) :
    LeanShared.TransientRestriction.generalizedKernel
      (LeanShared.TransientRestriction.block A B D) z k ≃ₗ[𝕜]
      LeanShared.TransientRestriction.generalizedKernel A z k :=
  LeanShared.TransientRestriction.generalizedRestrictionEquiv A B D hz N
    (nilpotent_of_uniform_finite_extinction C D hD N hext) k

/-- Uniform entrance-or-exit of every noise orbit gives operator nilpotence
for a *killed layer* chain, when its surviving finite paths have the actual
noise-orbit realization. This realization must be established from the noise
kernel; it is not supplied by the block-triangular algebra. -/
theorem nilpotent_of_noise_orbit_exit
    {Ω : ℕ → Type*} (F : (n : ℕ) → Ω n → X → X) (K : Set X) (N : ℕ)
    (hexit : ∀ η : (n : ℕ) → Ω n, ∀ x ∈ K, ∃ j ≤ N,
      LeanShared.nonautonomousOrbit (fun n => F n (η n)) x j ∉ K)
    (hpaths : ∀ x, ∀ᵐ ω ∂C.pathMeasure x, ω ∈ CanonicalChain.survival N →
      ∃ η : (n : ℕ) → Ω n, ∀ j ≤ N,
        ω j = some (LeanShared.nonautonomousOrbit (fun n => F n (η n)) x j) ∧
          LeanShared.nonautonomousOrbit (fun n => F n (η n)) x j ∈ K) : D ^ N = 0 := by
  apply nilpotent_of_uniform_finite_extinction C D hD N
  intro x
  have hn : ∀ᵐ ω ∂C.pathMeasure x, ω ∉ CanonicalChain.survival N := by
    filter_upwards [hpaths x] with ω hp
    intro hs
    obtain ⟨η, hη⟩ := hp hs
    have hx : x ∈ K := by simpa using (hη 0 (Nat.zero_le N)).2
    obtain ⟨j, hj, hbad⟩ := hexit η x hx
    exact hbad (hη j hj).2
  simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hn

end ConditionedStochasticStabilityHyperbolic.Restriction
