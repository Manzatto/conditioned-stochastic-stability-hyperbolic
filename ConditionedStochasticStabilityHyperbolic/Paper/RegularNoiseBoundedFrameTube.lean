module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformChartWords
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseCenteredWordOffsets
public import LeanShared.Analysis.CenteredFrameDerivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The literal Whitney hypotheses give common spatial and noise windows in
arbitrary bounded centered frames of a fixed chart pair. No continuity in
the noise scale or in the choices of frames is assumed. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared.CenteredManifoldCoordinates LeanShared.FiniteJetComposition

theorem Maps.uniform_centered_word_tube
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (B δ : ℝ) (oneB : 1 ≤ B) (positiveδ : 0 < δ) :
    ∃ radius > 0, ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ a ∈ K, ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ B → ‖R.symm.toContinuousLinearMap‖ ≤ B →
      ∀ b : E, ∀ z : P, ‖z‖ ≤ radius →
      let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
      let g := d ∘ (T : M → M)^[N] ∘ c.symm
      ‖centered L R a b f z - centered L R a b g z‖ +
        ‖fderiv ℝ (centered L R a b f) z - fderiv ℝ (centered L R a b g) z‖ ≤ δ := by
  have positiveB : 0 < B := lt_of_lt_of_le zero_lt_one oneB
  have positiveSquare : 0 < B ^ 2 := sq_pos_of_pos positiveB
  obtain ⟨ρ, positiveρ, η, positiveη, estimates⟩ := F.uniform_chart_word_tube
    regularity deterministic c d hc hd N K compact inside (δ / B ^ 2)
      (div_pos positiveδ positiveSquare)
  refine ⟨ρ / B, div_pos positiveρ positiveB, η, positiveη, ?_⟩
  intro ε hp hw controls a ha L R boundL boundR b z small
  dsimp only
  let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
  let g := d ∘ (T : M → M)^[N] ∘ c.symm
  have displacement : dist (a + L z) a ≤ ρ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    calc
      ‖L z‖ ≤ ‖L.toContinuousLinearMap‖ * ‖z‖ := L.toContinuousLinearMap.le_opNorm z
      _ ≤ B * (ρ / B) := mul_le_mul boundL small (norm_nonneg _) positiveB.le
      _ = ρ := by field_simp
  have raw := estimates ε hp hw controls a ha (a + L z) displacement
  change ‖f (a + L z) - g (a + L z)‖ +
    ‖fderiv ℝ f (a + L z) - fderiv ℝ g (a + L z)‖ ≤ δ / B ^ 2 at raw
  have squareBound : B ≤ B ^ 2 := by nlinarith
  have value := (centered_value_difference_le L R a b f g z).trans
    (mul_le_mul_of_nonneg_right (boundR.trans squareBound) (norm_nonneg _))
  have derivative := (centered_derivative_difference_le L R a b f g z).trans
    (mul_le_mul boundR
      (mul_le_mul_of_nonneg_left boundL (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) positiveB.le)
  have derivativeBound :
      ‖fderiv ℝ (centered L R a b f) z - fderiv ℝ (centered L R a b g) z‖ ≤
        B ^ 2 * ‖fderiv ℝ f (a + L z) - fderiv ℝ g (a + L z)‖ := by
    convert derivative using 1
    ring
  calc
    _ ≤ B ^ 2 * (‖f (a + L z) - g (a + L z)‖ +
        ‖fderiv ℝ f (a + L z) - fderiv ℝ g (a + L z)‖) := by
      rw [mul_add]
      exact add_le_add value derivativeBound
    _ ≤ B ^ 2 * (δ / B ^ 2) := mul_le_mul_of_nonneg_left raw positiveSquare.le
    _ = δ := by field_simp

theorem Maps.uniform_centered_word_c1_tube
    {E M ι P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {T : M ≃ₜ M} {r : ℝ} (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M)
    (hd : d ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (N : ℕ)
    (K : Set E) (compact : IsCompact K)
    (inside : K ⊆ c.target ∩ ((T : M → M)^[N] ∘ c.symm) ⁻¹' d.source)
    (B δ : ℝ) (oneB : 1 ≤ B) (positiveδ : 0 < δ) :
    ∃ radius > 0, ∃ η : ℝ≥0, 0 < η ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ controls : ℕ → cube (ι := ι) ε,
      ∀ a ∈ K, ∀ (L : P ≃L[ℝ] E) (R : Q ≃L[ℝ] E),
      ‖L.toContinuousLinearMap‖ ≤ B → ‖R.symm.toContinuousLinearMap‖ ≤ B →
      ∀ b : E, ∀ z : P, ‖z‖ ≤ radius →
      let f := d ∘ word (fun n => F.family ε (controls n).val) N ∘ c.symm
      let g := d ∘ (T : M → M)^[N] ∘ c.symm
      DifferentiableAt ℝ (centered L R a b f) z ∧
        ‖centered L R a b f z - centered L R a b g z‖ +
          ‖fderiv ℝ (centered L R a b f) z - fderiv ℝ (centered L R a b g) z‖ ≤ δ := by
  obtain ⟨radius, positiveRadius, η, positiveη, estimate⟩ :=
    F.uniform_centered_word_tube (P := P) (Q := Q) regularity deterministic c d hc hd N K compact inside B δ oneB positiveδ
  obtain ⟨radius', positiveRadius', η', positiveη', differentiable⟩ :=
    F.centered_word_offset_window (P := P) (Q := Q) regularity deterministic c d hc hd N K compact inside B δ
      (lt_of_lt_of_le zero_lt_one oneB) positiveδ
  refine ⟨min radius radius', lt_min positiveRadius positiveRadius',
    min η η', lt_min positiveη positiveη', ?_⟩
  intro ε hp hw controls a ha L R boundL boundR b z small
  exact ⟨(differentiable ε hp (hw.trans (min_le_right _ _)) controls a ha L R boundL boundR
    b z (small.trans (min_le_right _ _))).1,
    estimate ε hp (hw.trans (min_le_left _ _)) controls a ha L R boundL boundR
      b z (small.trans (min_le_left _ _))⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
