module

public import ConditionedStochasticStabilityHyperbolic.Spectral.InverseRegularTransfer
public import LeanShared.Analysis.CylinderPrincipalCoefficient

/-! Joint inverse-map/Jacobian continuity and ordinary lower-Hölder
interpolation imply continuity of the CONSTRUCTED full-test inverse action.
No continuity in the highest C^r topology, or derivative of a noise density,
is required. -/

public noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.InverseRegularTransfer
open LeanShared CylinderPrincipalCoefficient
variable {X Ω Test Core : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Ω] [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  {view : Test →ₗ[ℂ] (X → ℂ)} (inj : Function.Injective view)
  {H : Ω → X → X} {W : X × Ω → ℝ} (s : OrdinarySources view H W)

theorem continuous_operator_core
    (smooth : Core → Test)
    (hH : Continuous (fun z : Ω × X => H z.1 z.2))
    (hW : Continuous (fun z : Ω × X => W (z.2, z.1)))
    (hsmooth : ∀ c, Continuous (view (smooth c)))
    (θ : ℝ) (hθ : 0 < θ) (C : Core → Ω → ℝ)
    (interpolation : ∀ c a₀ a ε, 0 ≤ ε →
      (∀ x, ‖view (s.operator inj a (smooth c)) x - view (s.operator inj a₀ (smooth c)) x‖ ≤ ε) →
      dist (s.operator inj a (smooth c)) (s.operator inj a₀ (smooth c)) ≤ C c a₀ * ε ^ θ)
    (c : Core) : Continuous (fun a => s.operator inj a (smooth c)) := by
  have hjoint : Continuous (fun z : Ω × X => view (s.operator inj z.1 (smooth c)) z.2) := by
    simp_rw [s.operator_function inj]
    exact (Complex.continuous_ofReal.comp hW).mul ((hsmooth c).comp hH)
  apply continuous_iff_continuousAt.mpr
  intro a₀
  let f : Ω × X → ℝ := fun z =>
    ‖view (s.operator inj z.1 (smooth c)) z.2 - view (s.operator inj a₀ (smooth c)) z.2‖
  have hf : Continuous f := (hjoint.sub (hjoint.comp (continuous_const.prodMk continuous_snd))).norm
  let e : Ω → ℝ := coefficient univ univ f
  have he0 : e a₀ = 0 := by
    apply le_antisymm
    · apply csSup_le (s := values univ univ f a₀) (values_nonempty univ univ f a₀)
      intro y hy
      rcases hy with hy | ⟨x, _, rfl⟩
      · obtain rfl := mem_singleton_iff.mp hy
        exact le_rfl
      · simp [f]
    · exact coefficient_nonneg isCompact_univ isClosed_univ hf a₀
  have he : Tendsto e (𝓝 a₀) (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hv := upperSemicontinuous_coefficient isCompact_univ isClosed_univ hf a₀ ε
      (by change e a₀ < ε; rw [he0]; exact hε)
    filter_upwards [hv] with a ha
    change dist (coefficient univ univ f a) 0 < ε
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg (coefficient_nonneg isCompact_univ isClosed_univ hf a)] using ha
  have hb : Tendsto (fun a => C c a₀ * e a ^ θ) (𝓝 a₀) (𝓝 0) := by
    simpa only [Real.zero_rpow hθ.ne', mul_zero] using
      (tendsto_const_nhds.mul (he.rpow_const (Or.inr hθ.le)))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) _ hb
  intro a
  apply interpolation c a₀ a (e a)
  · exact coefficient_nonneg isCompact_univ isClosed_univ hf a
  · intro x
    exact density_le_coefficient isCompact_univ isClosed_univ hf a x ⟨mem_univ _, mem_univ _⟩

end ConditionedStochasticStabilityHyperbolic.InverseRegularTransfer
