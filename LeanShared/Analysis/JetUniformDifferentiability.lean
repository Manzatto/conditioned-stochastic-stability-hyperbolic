module
public import LeanShared.Analysis.JetUniformOnCompact
import all LeanShared.Analysis.FiniteJetComposition

/-! Moving-point C¹ convergence supplies uniform differentiability on a
compact set, as well as the uniform numerical jet bounds. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology NNReal

theorem uniformly_differentiable_on_compact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ω : ℝ≥0 → Type*) (f : (ε : ℝ≥0) → Ω ε → E → F) (g : E → F)
    (U K : Set E) (compact : IsCompact K) (subset : K ⊆ U)
    (converges : ∀ (ε : ℕ → ℝ≥0) (ω : ∀ n, Ω (ε n)),
      Tendsto ε atTop (𝓝 0) → (∀ n, 0 < ε n) →
      JetConvergesOn (fun n => f (ε n) (ω n)) g atTop U) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η → ∀ ω : Ω ε,
      ∀ x ∈ K, DifferentiableAt ℝ (f ε ω) x := by
  by_contra! failure
  have failures (n : ℕ) :
      ∃ ε : ℝ≥0, 0 < ε ∧ ε ≤ 1 / ((n : ℝ≥0) + 1) ∧ ∃ ω : Ω ε,
        ∃ x ∈ K, ¬ DifferentiableAt ℝ (f ε ω) x :=
    failure (1 / ((n : ℝ≥0) + 1)) (by positivity)
  choose ε positiveε small ω x inside bad using failures
  have limitε : Tendsto ε atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    exact squeeze_zero (fun n => (ε n).property)
      (fun n => by exact_mod_cast small n) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨p, hp, φ, increasing, limitx⟩ := compact.tendsto_subseq inside
  have jets := converges (ε ∘ φ) (fun n => ω (φ n)) (limitε.comp increasing.tendsto_atTop)
    (fun n => positiveε (φ n))
  obtain ⟨n, hn⟩ := ((jets p (subset hp)).2 (x ∘ φ) limitx).2.2.exists
  exact bad (φ n) hn

end LeanShared.FiniteJetComposition
