module

public import LeanShared.Analysis.UniformTwoNormResolventStability
public import LeanShared.Analysis.WeakResolventDifference
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Uniform actual weak-resolvent convergence under KL two-norm hypotheses,
for arbitrary parameter filters and arbitrary deterministic resolvent subsets. -/

public section
open Filter Topology ContinuousLinearMap
namespace LeanShared.UniformTwoNormResolventConvergence
variable {E W I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Actual resolvents are uniformly bounded and converge uniformly in the
weak operator norm on bounded deterministic resolvent sets outside the strong
disk. Only weak perturbations tend to zero. -/
theorem exists_bound_and_convergence (P : I → E →L[ℂ] E) (Q : E →L[ℂ] E)
    (i : E →L[ℂ] W) (l : Filter I) (Ω : Set ℂ)
    (α M C D Cw r outer bound L : ℝ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hCw : 0 ≤ Cw)
    (hr : α < r) (houter : 0 ≤ outer) (hbound : 0 ≤ bound) (hL : 0 ≤ L)
    (strongQ : ∀ n x, ‖(Q ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖)
    (weakQ : ∀ n x, ‖i ((Q ^ n) x)‖ ≤ Cw * M ^ n * ‖i x‖)
    (region : ∀ z ∈ Ω, r ≤ ‖z‖ ∧ ‖z‖ ≤ outer ∧
      z ∈ resolventSet ℂ Q ∧ ‖resolvent Q z‖ ≤ L)
    (good : ∀ᶠ ε in l, ‖P ε‖ ≤ bound ∧
      (∀ n x, ‖(P ε ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * M ^ n * ‖i x‖) ∧
      ∀ z ∈ Ω, Function.Injective (z • (1 : E →L[ℂ] E) - P ε) →
        DenseRange (z • (1 : E →L[ℂ] E) - P ε))
    (perturbation : Tendsto (fun ε => ‖i.comp (P ε - Q)‖) l (𝓝 0)) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ᶠ ε in l, ∀ z ∈ Ω, z ∈ resolventSet ℂ (P ε) ∧ ‖resolvent (P ε) z‖ ≤ K) ∧
      ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in l, ∀ z ∈ Ω,
        ‖i.comp (resolvent (P ε) z - resolvent Q z)‖ ≤ δ := by
  obtain ⟨τ0, K, hτ0, hK, stable⟩ := UniformTwoNormResolventStability.exists_bound Q i
    α M C D Cw r outer bound L hα hM hC hD hCw hr houter hbound hL strongQ weakQ
  have bounded : ∀ᶠ ε in l, ∀ z ∈ Ω,
      z ∈ resolventSet ℂ (P ε) ∧ ‖resolvent (P ε) z‖ ≤ K := by
    filter_upwards [good, perturbation.eventually (gt_mem_nhds hτ0)] with ε hgood hsmall
    intro z hz
    have hzregion := region z hz
    exact stable (P ε) hgood.1 hgood.2.1 hsmall.le z hzregion.1 hzregion.2.1
      hzregion.2.2.1 hzregion.2.2.2 (hgood.2.2 z hz)
  refine ⟨K, hK, bounded, fun δ hδ => ?_⟩
  let J := bound + ‖Q‖
  have hJ : 0 ≤ J := add_nonneg hbound (norm_nonneg Q)
  obtain ⟨η, hη, hηsmall⟩ := exists_pos_mul_lt (half_pos hδ) (J * K)
  obtain ⟨Cweak, hCweak, weakResolver⟩ := UniformWeakResolventBound.exists_bound Q i
    α M C D Cw r outer L hα hM hC hD hCw hr houter hL strongQ weakQ η hη
  obtain ⟨τ, hτ, hτsmall⟩ := exists_pos_mul_lt (half_pos hδ) (Cweak * K)
  filter_upwards [good, bounded, perturbation.eventually (gt_mem_nhds hτ)] with ε hgood hbounded hsmall
  intro z hz
  have hzregion := region z hz
  have normDifference : ‖P ε - Q‖ ≤ J := (norm_sub_le _ _).trans (add_le_add hgood.1 le_rfl)
  have weakDifference := WeakResolventDifference.norm_le (P ε) Q i z
    (hbounded z hz).1 hzregion.2.2.1 η Cweak J τ K hη.le hCweak hJ hτ.le hK
    (weakResolver z hzregion.1 hzregion.2.1 hzregion.2.2.1 hzregion.2.2.2)
    normDifference hsmall.le (hbounded z hz).2
  exact weakDifference.trans (by nlinarith)

end LeanShared.UniformTwoNormResolventConvergence
