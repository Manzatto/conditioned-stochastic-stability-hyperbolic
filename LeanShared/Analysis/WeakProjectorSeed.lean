module
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity

/-! A fixed deterministic vector supplies a weakly convergent, strongly
bounded seed for noisy projectors. No completeness of the weak target is needed. -/
public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.WeakProjectorSeed
variable {E W I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem tendsto_and_bound (P : I → E →L[ℂ] E) (P₀ : E →L[ℂ] E)
    (i : E →L[ℂ] W) (v₀ : E) (fixed : P₀ v₀=v₀) (l : Filter I) (C : ℝ)
    (convergence : Tendsto (fun ε => i.comp (P ε-P₀)) l (𝓝 0))
    (coercivity : ∀ᶠ ε in l, ∀ x : E, ‖P ε x‖ ≤ C*‖i (P ε x)‖) :
    Tendsto (fun ε => i (P ε v₀)) l (𝓝 (i v₀)) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ ε in l, ‖P ε v₀‖ ≤ B := by
  have evaluated := ((ContinuousLinearMap.apply ℂ W v₀).continuous.tendsto
    (0 : E →L[ℂ] W)).comp convergence
  change Tendsto (fun ε => i ((P ε-P₀) v₀)) l (𝓝 0) at evaluated
  have difference : Tendsto (fun ε => i (P ε v₀)-i v₀) l (𝓝 0) := by
    simpa only [comp_apply,sub_apply,map_sub,fixed,zero_apply] using evaluated
  have vectors : Tendsto (fun ε => i (P ε v₀)) l (𝓝 (i v₀)) := by
    simpa only [sub_add_cancel,zero_add] using difference.add_const (i v₀)
  refine ⟨vectors,(abs C)*(‖i v₀‖+1),mul_nonneg (abs_nonneg _) (by positivity),?_⟩
  have normBound := vectors.norm.eventually (gt_mem_nhds (lt_add_one ‖i v₀‖))
  filter_upwards [coercivity,normBound] with ε hε hn
  exact (hε v₀).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hn.le (abs_nonneg C)))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem normalized_functional (w : W) (nonzero : w ≠ 0) :
    ∃ ψ : W →L[ℂ] ℂ, ψ w=1 := by
  obtain ⟨ψ,_,value⟩ := exists_dual_vector ℂ w (norm_ne_zero_iff.mpr nonzero)
  refine ⟨(‖w‖ : ℂ)⁻¹ • ψ,?_⟩
  simp only [smul_apply,smul_eq_mul,value]
  exact inv_mul_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr nonzero)
end LeanShared.WeakProjectorSeed
