module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseCenteredWords
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseCenteredWordForcing
public import LeanShared.Analysis.CenteredOffsetChange

/-! Actual noisy word estimates at an arbitrary reference target offset.
Derivative perturbations ignore the offset; centered forcing differences
retain the exact original noise. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold
open scoped Topology Manifold ContDiff NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates

theorem InverseFamily.centered_word_offset_window
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T.symm : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (C δ : ℝ) (positiveC : 0 < C) (positiveδ : 0 < δ) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ a ∈ K, ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ C → ‖R.symm.toContinuousLinearMap‖ ≤ C →
      let f := d ∘ word (fun n => fun y => J.map ε ((controls n).val,y)) N ∘ c.symm
      let g := d ∘ (T.symm : M → M)^[N] ∘ c.symm
      ∀ b : E, ∀ z : P, ‖z‖ ≤ radius →
        DifferentiableAt ℝ (centered L R a b f) z ∧
        ‖fderiv ℝ (centered L R a b f) z -
          fderiv ℝ (centered L R a b g) z‖ ≤ δ := by
  obtain ⟨radius,positiveRadius,η,positiveη,bounds⟩ := J.centered_word_window (P := P) (Q := Q) regularity deterministic inverse
    c d hc hd N K compact inside C δ positiveC positiveδ
  refine ⟨radius,positiveRadius,η,positiveη,fun ε hp hw controls a ha L R boundL boundR b z hz => ?_⟩
  have result := (bounds ε hp hw controls a ha L R boundL boundR).2 z hz
  let f := d ∘ word (fun n => fun y => J.map ε ((controls n).val,y)) N ∘ c.symm
  let g := d ∘ (T.symm : M → M)^[N] ∘ c.symm
  refine ⟨differentiableAt_centered_offset L R a (g a) b f z result.1,?_⟩
  rw [fderiv_centered_offset L R a b (g a) f z,
    fderiv_centered_offset L R a b (g a) g z]
  exact result.2

theorem InverseFamily.centered_word_noise_forcing_window
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r : ℝ} {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T.symm : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (C θ : ℝ) (positiveC : 0 < C) (positiveθ : 0 < θ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ a ∈ K,
      ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E), ‖R.symm.toContinuousLinearMap‖ ≤ C →
      let f := d ∘ word (fun n => fun y => J.map ε ((controls n).val,y)) N ∘ c.symm
      let g := d ∘ (T.symm : M → M)^[N] ∘ c.symm
      ∀ b : E, ‖centered L R a b f 0 - centered L R a b g 0‖ ≤ θ := by
  obtain ⟨η,positiveη,bounds⟩ := J.centered_word_forcing_window (P := P) (Q := Q) regularity deterministic inverse
    c d hc hd N K compact inside C θ positiveC positiveθ
  refine ⟨η,positiveη,fun ε hp hw controls a ha L R boundR b => ?_⟩
  rw [centered_noise_difference_zero]
  exact bounds ε hp hw controls a ha L R boundR

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
