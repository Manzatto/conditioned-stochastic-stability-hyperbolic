module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Weak convergence of actual operator applications when only the operator
perturbation in a weaker norm tends to zero. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.TwoNormApplicationConvergence
variable {E W I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Uniformly strongly bounded, weakly convergent vectors may be tested by
weakly perturbing operators whose deterministic action is weakly bounded. -/
theorem tendsto (P : I → E →L[ℂ] E) (Q : E →L[ℂ] E) (i : E →L[ℂ] W)
    (v : I → E) (v₀ : E) (l : Filter I) (B C : ℝ)
    (bounded : ∀ᶠ ε in l, ‖v ε‖ ≤ B)
    (vectors : Tendsto (fun ε => i (v ε)) l (𝓝 (i v₀)))
    (perturbation : Tendsto (fun ε => ‖i.comp (P ε - Q)‖) l (𝓝 0))
    (weakQ : ∀ x, ‖i (Q x)‖ ≤ C * ‖i x‖) :
    Tendsto (fun ε => i ((P ε) (v ε))) l (𝓝 (i (Q v₀))) := by
  have vdiff : Tendsto (fun ε => ‖i (v ε - v₀)‖) l (𝓝 0) := by
    have hh := (vectors.sub_const (i v₀)).norm
    simpa only [map_sub, sub_self, norm_zero] using hh
  have upper : Tendsto (fun ε => ‖i.comp (P ε - Q)‖ * B + C * ‖i (v ε - v₀)‖) l (𝓝 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using
      (perturbation.mul_const B).add (vdiff.const_mul C)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ upper
  filter_upwards [bounded] with ε hε
  have identity : i ((P ε) (v ε)) - i (Q v₀) =
      i ((P ε - Q) (v ε)) + i (Q (v ε - v₀)) := by
    simp only [sub_apply, map_sub]
    abel
  rw [identity]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (weakQ (v ε - v₀))
  exact ((i.comp (P ε - Q)).le_opNorm (v ε)).trans
    (mul_le_mul_of_nonneg_left hε (norm_nonneg _))

end LeanShared.TwoNormApplicationConvergence
