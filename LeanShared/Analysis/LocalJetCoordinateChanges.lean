module
public import LeanShared.Analysis.FiniteJetComposition
import all LeanShared.Analysis.FiniteJetComposition
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! Moving-point C¹ convergence is invariant under fixed smooth coordinate
changes and under equality on an actual open chart domain. These are derived
calculus facts used to join the different charts of a finite noisy itinerary. -/
public noncomputable section
namespace LeanShared.FiniteJetComposition
open Set Filter
open scoped Topology

theorem JetConvergesOn.constant
    {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (l : Filter A) (U : Set E)
    (smooth : ∀ x ∈ U, ContDiffAt ℝ 1 g x) :
    JetConvergesOn (fun _ : A => g) g l U := by
  apply of_local_bounds _ _ l U smooth
  intro x hx v hv
  refine ⟨fun _ => 0, tendsto_const_nhds, ?_, ?_, ?_⟩
  · exact Eventually.of_forall (fun _ => by rw [sub_self, norm_zero])
  · exact Eventually.of_forall (fun _ => by rw [sub_self, norm_zero])
  · have near := hv.eventually ((smooth x hx).eventually (by norm_num))
    exact near.mono (fun _ h => h.differentiableAt (by norm_num))

theorem JetConvergesOn.mono
    {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : A → E → F} {g : E → F} {l : Filter A} {U V : Set E}
    (h : JetConvergesOn f g l U) (subset : V ⊆ U) : JetConvergesOn f g l V :=
  fun x hx => h x (subset hx)

theorem JetConvergesOn.congr_on_open
    {A E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : A → E → F} {f₀ g₀ : E → F} {l : Filter A} {U : Set E}
    (h : JetConvergesOn f f₀ l U) (openU : IsOpen U)
    (same : ∀ᶠ a in l, EqOn (f a) (g a) U) (reference : EqOn f₀ g₀ U) :
    JetConvergesOn g g₀ l U := by
  intro x hx
  have referenceGerm : f₀ =ᶠ[𝓝 x] g₀ := by
    filter_upwards [openU.mem_nhds hx] with y hy
    exact reference hy
  have old := h x hx
  refine ⟨referenceGerm.differentiableAt_iff.mp old.1, fun v hv => ?_⟩
  have limits := old.2 v hv
  have inside := hv.eventually (openU.mem_nhds hx)
  have germs : ∀ᶠ a in l, f a =ᶠ[𝓝 (v a)] g a := by
    filter_upwards [same, inside] with a ha hi
    filter_upwards [openU.mem_nhds hi] with y hy
    exact ha hy
  have valueLimit := limits.1
  have derivativeLimit := limits.2.1
  rw [referenceGerm.self_of_nhds] at valueLimit
  rw [referenceGerm.fderiv_eq] at derivativeLimit
  refine ⟨valueLimit.congr' ?_, derivativeLimit.congr' ?_, ?_⟩
  · exact germs.mono (fun _ ha => ha.self_of_nhds)
  · exact germs.mono (fun _ ha => ha.fderiv_eq)
  · filter_upwards [germs, limits.2.2] with a ha hd
    exact ha.differentiableAt_iff.mp hd

end LeanShared.FiniteJetComposition
