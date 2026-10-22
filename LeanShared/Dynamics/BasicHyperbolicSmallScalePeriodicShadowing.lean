module
public import LeanShared.Dynamics.BasicHyperbolicOneStepBowen
public import LeanShared.Dynamics.BasicHyperbolicWeightedPeriodicShadowing

/-! Actual fractional potentials and mixing hyperbolic basic data give periodic weighted sums dominating every finite separated orbit sum. All Bowen, closing and transition costs are derived. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle NNReal BigOperators
open ThermodynamicDefinitions

set_option maxHeartbeats 2400000 in
theorem BasicData.small_scale_weighted_periodic_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ V : Set M} (b : BasicData (E := E) T Λ V)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    (mixing : MixingOn T Λ)
    (ψ : M → ℝ) (α : ℝ) (positiveα : 0 < α) (smallα : α < 1)
    (regular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) α ψ)
    (ρ : ℝ) (positiveρ : 0 < ρ) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ gap : ℕ, 0 < gap ∧ ∃ c > 0,
      ∀ n : ℕ, ∀ s : Finset M, Separated T Λ (n + 1) (3 * ε) s →
      ∃ q : Finset M, Separated T Λ (n + gap) ε q ∧
        (∀ z ∈ q, (T : M → M)^[n + gap] z = z) ∧
        c * (∑ x ∈ s, Real.exp (orbitSum T ψ (n + 1) x)) ≤
          ∑ z ∈ q, Real.exp (orbitSum T ψ (n + gap) z) := by
  obtain ⟨η, positiveη, D, _, bowen⟩ :=
    b.bowen_distortion forward inverse ψ α positiveα smallα regular
  let ε := min η ρ
  have positiveε : 0 < ε := lt_min positiveη positiveρ
  have εsmall : ε ≤ η := min_le_left _ _
  have continuous : Continuous ψ := regular.differentiable.continuous
  obtain ⟨B, _, bounded⟩ :=
    (b.hyperbolic.compact.image continuous).isBounded.exists_pos_norm_le
  have lower (x : M) (hx : x ∈ Λ) : -B ≤ ψ x :=
    (abs_le.mp (by simpa only [Real.norm_eq_abs] using bounded (ψ x) ⟨x, hx, rfl⟩)).1
  obtain ⟨gap, positiveGap, closes⟩ := b.weighted_periodic_shadowing forward inverse
    mixing ε positiveε ψ B D lower
    (fun n x hx y hy close => bowen (n + 1) x hx y hy
      (fun j hj => (close j (by omega)).trans_le εsmall))
  exact ⟨ε, positiveε, min_le_right _ _, gap, positiveGap,
    Real.exp (-(D + (gap - 1 : ℕ) * B)), Real.exp_pos _, closes⟩

end LeanShared.HyperbolicBasicSet
