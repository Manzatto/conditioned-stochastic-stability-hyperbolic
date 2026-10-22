module
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-! C¹ perturbations composed a finite number of times. Moving-point jet
convergence captures the consequence of local Whitney estimates. The chain
rule proves it is preserved by actual composition; no iterated perturbation
estimate or differentiability of the varying family in its index is assumed. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

def JetConvergesOn
    {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : A → E → F) (g : E → F) (l : Filter A) (U : Set E) : Prop :=
  ∀ x ∈ U, DifferentiableAt ℝ g x ∧ ∀ v : A → E, Tendsto v l (𝓝 x) →
    Tendsto (fun a => f a (v a)) l (𝓝 (g x)) ∧
    Tendsto (fun a => fderiv ℝ (f a) (v a)) l (𝓝 (fderiv ℝ g x)) ∧
    ∀ᶠ a in l, DifferentiableAt ℝ (f a) (v a)

theorem of_local_bounds
    {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : A → E → F) (g : E → F) (l : Filter A) (U : Set E)
    (smooth : ∀ x ∈ U, ContDiffAt ℝ 1 g x)
    (bounds : ∀ x ∈ U, ∀ v : A → E, Tendsto v l (𝓝 x) →
      ∃ δ : A → ℝ, Tendsto δ l (𝓝 0) ∧
        (∀ᶠ a in l, ‖f a (v a) - g (v a)‖ ≤ δ a) ∧
        (∀ᶠ a in l, ‖fderiv ℝ (f a) (v a) - fderiv ℝ g (v a)‖ ≤ δ a) ∧
        ∀ᶠ a in l, DifferentiableAt ℝ (f a) (v a)) :
    JetConvergesOn f g l U := by
  intro x hx
  refine ⟨(smooth x hx).differentiableAt (by norm_num), fun v hv => ?_⟩
  obtain ⟨δ, limit, values, derivatives, differentiable⟩ := bounds x hx v hv
  have value_error := squeeze_zero_norm' values limit
  have derivative_error := squeeze_zero_norm' derivatives limit
  have value_limit := (smooth x hx).continuousAt.tendsto.comp hv
  have derivative_limit := ((smooth x hx).continuousAt_fderiv (by norm_num)).tendsto.comp hv
  refine ⟨?_, ?_, differentiable⟩
  · have result := value_error.add value_limit
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using result
  · have result := derivative_error.add derivative_limit
    simpa only [Function.comp_apply, sub_add_cancel, zero_add] using result

theorem JetConvergesOn.comp
    {A E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : A → F → G} {f₀ : F → G} {g : A → E → F} {g₀ : E → F}
    {l : Filter A} {U : Set F} {V : Set E}
    (outer : JetConvergesOn f f₀ l U) (inner : JetConvergesOn g g₀ l V)
    (maps : MapsTo g₀ V U) :
    JetConvergesOn (fun a => f a ∘ g a) (f₀ ∘ g₀) l V := by
  intro x hx
  have inner_at := inner x hx
  have outer_at := outer (g₀ x) (maps hx)
  refine ⟨outer_at.1.comp x inner_at.1, fun v hv => ?_⟩
  have gi := inner_at.2 v hv
  have fi := outer_at.2 (fun a => g a (v a)) gi.1
  refine ⟨fi.1, ?_, ?_⟩
  · have composition : Continuous (fun p : (F →L[ℝ] G) × (E →L[ℝ] F) => p.1.comp p.2) :=
      continuous_fst.clm_comp continuous_snd
    have limit := (composition.tendsto _).comp (fi.2.1.prodMk_nhds gi.2.1)
    rw [fderiv_comp x outer_at.1 inner_at.1]
    apply limit.congr'
    filter_upwards [fi.2.2, gi.2.2] with a ha hb
    exact (fderiv_comp (v a) ha hb).symm
  · filter_upwards [fi.2.2, gi.2.2] with a ha hb
    exact ha.comp (v a) hb

end LeanShared.FiniteJetComposition
