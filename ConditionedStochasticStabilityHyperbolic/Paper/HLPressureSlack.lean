module

public import ConditionedStochasticStabilityHyperbolic.Paper.HLPrincipalRate
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Strict pressure slack from the derived HL hyperbolicity rate. The
comparison premise concerns the full actual survivor-cylinder pressure with
its positive-envelope perturbation, not only density values on the core. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Manifold ContDiff Bundle
namespace ConditionedStochasticStabilityHyperbolic.Paper.HL
open LeanShared
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ V : Set M} (h : HL (E := E) T g Λ V)

/-- A classical deterministic survivor-cover comparison at envelopes whose
pressure increase is at most δ yields strict slack internally. No strict
coefficient bound or noisy operator estimate is assumed. -/
theorem exists_pressure_slack {t s : ℝ} (ht : 0 < t) (hs : s < 0)
    (P : ℝ) (Q : ℝ → ℝ)
    (comparison : ∀ δ, 0 < δ → Q δ ≤ h.principalRate t s * Real.exp (P + δ)) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ Q δ < ρ ∧ ρ < Real.exp P := by
  let γ := h.principalRate t s
  have hγpos : 0 < γ := h.principalRate_pos t s
  have hγlt : γ < 1 := h.principalRate_lt_one ht hs
  have hlog : Real.log γ < 0 := Real.log_neg hγpos hγlt
  let δ := -(Real.log γ) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsum : Real.log γ + δ < 0 := by dsimp [δ]; linarith
  have hfactor : γ * Real.exp δ < 1 := by
    calc
      γ * Real.exp δ = Real.exp (Real.log γ + δ) := by
        rw [Real.exp_add, Real.exp_log hγpos]
      _ < 1 := Real.exp_lt_one_iff.mpr hsum
  have hQ : Q δ < Real.exp P := (comparison δ hδ).trans_lt (by
    calc
      γ * Real.exp (P + δ) = Real.exp P * (γ * Real.exp δ) := by
        rw [Real.exp_add]; ring
      _ < Real.exp P * 1 := mul_lt_mul_of_pos_left hfactor (Real.exp_pos P)
      _ = Real.exp P := mul_one _)
  let ρ := (max (Q δ) 0 + Real.exp P) / 2
  have hmax : max (Q δ) 0 < Real.exp P := max_lt hQ (Real.exp_pos P)
  refine ⟨δ, ρ, hδ, ?_, ?_, ?_⟩
  · dsimp [ρ]; linarith [le_max_right (Q δ) 0, Real.exp_pos P]
  · dsimp [ρ]; linarith [le_max_left (Q δ) 0]
  · dsimp [ρ]; linarith

end ConditionedStochasticStabilityHyperbolic.Paper.HL
