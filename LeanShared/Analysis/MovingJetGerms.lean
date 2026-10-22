module
public import LeanShared.Analysis.LocalJetCoordinateChanges
import all LeanShared.Analysis.FiniteJetComposition

/-! Local equality may depend on the moving base point and on the noise.
This permits telescoping actual finite noisy chart words without asserting
one global coordinate domain valid for every sufficiently small perturbation. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

theorem JetConvergesOn.congr_moving_germs
    {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : A → E → F} {f₀ g₀ : E → F} {l : Filter A} {U : Set E}
    (h : JetConvergesOn f f₀ l U)
    (reference : ∀ x ∈ U, f₀ =ᶠ[𝓝 x] g₀)
    (same : ∀ x ∈ U, ∀ v : A → E, Tendsto v l (𝓝 x) →
      ∀ᶠ a in l, f a =ᶠ[𝓝 (v a)] g a) :
    JetConvergesOn g g₀ l U := by
  intro x hx
  have ref := reference x hx
  have old := h x hx
  refine ⟨ref.differentiableAt_iff.mp old.1, fun v hv => ?_⟩
  have limits := old.2 v hv
  have germs := same x hx v hv
  have values := limits.1
  have derivatives := limits.2.1
  rw [ref.self_of_nhds] at values
  rw [ref.fderiv_eq] at derivatives
  refine ⟨values.congr' ?_, derivatives.congr' ?_, ?_⟩
  · exact germs.mono (fun _ ha => ha.self_of_nhds)
  · exact germs.mono (fun _ ha => ha.fderiv_eq)
  · filter_upwards [germs, limits.2.2] with a ha hd
    exact ha.differentiableAt_iff.mp hd

end LeanShared.FiniteJetComposition
