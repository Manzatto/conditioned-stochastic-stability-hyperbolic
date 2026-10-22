module
public import LeanShared.Dynamics.BasicHyperbolicOneStepBowen
public import LeanShared.Dynamics.BasicHyperbolicWeightedGluing

/-! Actual regular mixing hyperbolic data give a uniform positive product
lower bound for weighted separated sums. Distortion, transition points,
separation and energy bounds are all constructed internally. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators
open ThermodynamicDefinitions

set_option maxHeartbeats 2400000 in
theorem BasicData.regular_weighted_gluing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ) :
    ∃ ε > 0, ∃ gap : ℕ, 0 < gap ∧ ∃ c > 0,
      ∀ n m : ℕ, ∀ s t : Finset M,
      Separated T Λ (n + 1) (3 * ε) s → Separated T Λ (m + 1) (3 * ε) t →
      ∃ q : Finset M, Separated T Λ (n + gap + m + 1) ε q ∧
        c * (∑ x ∈ s, Real.exp (orbitSum T ψ (n + 1) x)) *
          (∑ y ∈ t, Real.exp (orbitSum T ψ (m + 1) y)) ≤
            ∑ z ∈ q, Real.exp (orbitSum T ψ (n + gap + m + 1) z) := by
  obtain ⟨ε, positiveε, D, _, bowen⟩ :=
    b.bowen_distortion forward inverse ψ α positiveα smallα regular
  have continuous : Continuous ψ := regular.differentiable.continuous
  obtain ⟨B, _, bounded⟩ :=
    (b.hyperbolic.compact.image continuous).isBounded.exists_pos_norm_le
  have lower (x : M) (hx : x ∈ Λ) : -B ≤ ψ x :=
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using bounded (ψ x) ⟨x, hx, rfl⟩)).1
  obtain ⟨gap, positiveGap, gluing⟩ := b.weighted_separated_gluing forward
    (inverse.mdifferentiable one_ne_zero) mixing ε positiveε ψ B D lower
    (fun n x hx y hy close => bowen (n + 1) x hx y hy (fun j hj => close j (by omega)))
  exact ⟨ε, positiveε, gap, positiveGap,
    Real.exp (-(2 * D + (gap - 1 : ℕ) * B)), Real.exp_pos _, gluing⟩

end LeanShared.HyperbolicBasicSet
