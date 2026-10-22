module

public import LeanShared.Dynamics.ControlledPlaqueClosure
public import LeanShared.Probability.EigenvectorSupport
public import LeanShared.Probability.NoiseEigenmeasureSupport
public import LeanShared.Probability.PositiveSupportLocalization

/-!
# Actual eigenmeasure specialization of random plaque positivity

The left eigenmeasure identity gives exact backward parents. Normalization
gives a positive supported seed, and localization of the product measure
places every positive supported point in the live interior. Thus neither
positive backward orbits nor positivity on the basic set are hypotheses.

The remaining classical random plaque inputs are lower semicontinuity,
existence of backward plaque orbits, and capture after an eventual backward
tail in a fixed geometric neighborhood. The fixed neighborhood is chosen
before the noise tolerance and independently of the eigenfunction.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace LeanShared.RandomPlaquePositivity

open ControlledPlaqueClosure NoiseEigenmeasureSupport

variable {X Ω : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Ω] [CompactSpace Ω]

/-- Steps 1--3 of the support proof with actual eigenmeasure data and a
noncircular tolerance. Zero propagation is the continuous eigenfunction's
consequence of its eigenfunction law and full noise support; it is separate
from the classical random plaque geometry. -/
theorem exists_pos_noise_tolerance_for_eigenfunction_positivity
    (T : X ≃ₜ X) (V K G : Set X)
    (hVK : V ⊆ K) (hK : IsCompact K) (hG : IsOpen G)
    (hcoreV : isolatedCore T K ⊆ V) (hcoreG : isolatedCore T K ⊆ G)
    (htrans : forwardTransitiveOn T (isolatedCore T K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (F : X × Ω → X) (zero : Ω),
      Continuous F →
      (∀ x, F (x, zero) = T x) →
      (∀ ω : Ω, ∀ x ∈ K, dist (F (x, ω)) (T x) < δ) →
      (∀ p ∈ isolatedCore T K, ∃ W : Set X, IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧
        ∀ y ∈ W, ∃ ω : Ω, F (T.symm p, ω) = y) →
      ∀ plaque : (ℤ → Ω) → Set X,
      (∀ ω : ℤ → Ω, ∀ ωn : ℕ → ℤ → Ω, Tendsto ωn atTop (𝓝 ω) →
        ∀ z ∈ plaque ω, ∃ zn : ℕ → X, Tendsto zn atTop (𝓝 z) ∧
          ∀ k, zn k ∈ plaque (ωn k)) →
      (∀ ω : ℤ → Ω, ∀ z ∈ plaque ω, ∃ b : ℕ → X, b 0 = z ∧
        (∀ n, b n ∈ V) ∧ ∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
      (∀ ω : ℤ → Ω, ∀ b : ℕ → X, (∀ n, b n ∈ V) →
        (∀ n, F (b (n + 1), backwardNoise ω n) = b n) →
        (∀ᶠ n : ℕ in atTop, b n ∈ G) →
          ∃ j : ℕ, b j ∈ plaque (backwardShift ω j)) →
      ∀ (κ : Kernel X X) (μ : Measure X) (r : ℝ≥0∞),
      r ≠ 0 → κ ∘ₘ μ = r • μ → (∀ᵐ x ∂μ, x ∈ μ.support) →
      μ.support ⊆ K →
      (∀ x ∈ μ.support, ∀ᵐ y ∂κ x, ∃ ω : Ω, F (x, ω) = y) →
      ∀ g : X → ℝ, Measurable g → ContinuousOn g K → (∀ x ∈ K, 0 ≤ g x) →
      (∀ x ∈ K, ∀ ω : Ω, F (x, ω) ∈ V → g x = 0 → g (F (x, ω)) = 0) →
      (∫ x, g x ∂μ) = 1 → (eigenvectorMeasure μ g).support ⊆ V →
      ∀ x ∈ isolatedCore T K, 0 < g x := by
  obtain ⟨δ, hδ, hpositivity⟩ :=
    exists_pos_noise_tolerance_for_core_positivity (Ω := Ω)
      T V K G hVK hK hG hcoreV hcoreG htrans
  refine ⟨δ, hδ, ?_⟩
  intro F zero hF hFzero hnoise hcover plaque hlsc hback hcapture
    κ μ r hr heigen hμae hSK hstep g hg hgc hg0 hzeroStep hnorm hlocal
  have hμcompact : IsCompact μ.support := μ.isClosed_support.isCompact
  have hparent : ∀ p ∈ μ.support, ∃ x ∈ μ.support, ∃ ω : Ω, F (x, ω) = p := by
    intro p hp
    exact exists_support_parent κ μ hμcompact hμae r hr heigen
      id continuous_id F hF hstep p hp
  have hμK : ∀ᵐ x ∂μ, x ∈ K := hμae.mono hSK
  have hlive : ∀ x ∈ μ.support, 0 < g x → x ∈ V := by
    intro x hx hxpos
    exact PositiveSupportLocalization.mem_live_of_pos_supported μ K V hμK
      g hg hgc hlocal hx (hSK hx) hxpos
  have hseed : ∃ p ∈ μ.support, 0 < g p :=
    exists_support_pos_of_integral_pos μ g hμae (by rw [hnorm]; exact zero_lt_one)
  exact hpositivity F zero hFzero hnoise hcover plaque hlsc hback hcapture
    g hgc hg0 hzeroStep μ.support hSK hlive hparent hseed

end LeanShared.RandomPlaquePositivity
