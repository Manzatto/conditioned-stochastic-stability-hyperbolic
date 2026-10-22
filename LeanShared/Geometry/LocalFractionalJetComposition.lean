module
public import LeanShared.Geometry.LocalFractionalJetBilinear
public import LeanShared.Analysis.LocalHolderComposition
public import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! Genuine all-order fractional chart transport. Smooth coordinate changes
preserve the top derivative Holder condition, by derivative induction and
the proved bounded-bilinear fractional rule. -/
public noncomputable section
namespace LeanShared.FractionalManifoldRegularity.JetAt
open Set Filter
open scoped Topology ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 3200000 in
theorem comp_smooth (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ {F G : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} {g : E → F} {x : E},
      JetAt n a f (g x) → ContDiffAt ℝ ∞ g x → JetAt n a (f ∘ g) x := by
  induction n with
  | zero =>
    intro F G _ _ _ _ f g x hf hg
    obtain ⟨U,openU,inU,C,hC,boundF⟩ := hf.holder
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,
      LinearIsometryEquiv.norm_map] at boundF
    obtain ⟨W,openW,inW,_maps,A,hA,bound⟩ := LocalHolderComposition.exists_bound ha hC
      (hg.of_le (by simp)) (openU.mem_nhds inU) boundF
    refine ⟨hf.smooth.comp x (hg.of_le (by simp)),W,openW,inW,A,hA,?_⟩
    intro y hy z hz
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,
      LinearIsometryEquiv.norm_map] using bound y hy z hz
  | succ n ih =>
    intro F G _ _ _ _ f g x hf hg
    have composed := ih hf.derivative hg
    have smoothDG : ContDiffAt ℝ ∞ (fderiv ℝ g) x := hg.fderiv_right (by simp)
    have derivativeG : JetAt n a (fderiv ℝ g) x :=
      of_contDiff_succ ha1 (smoothDG.of_le (by simp))
    have product := bilinear n ha ha1 (ContinuousLinearMap.compL ℝ E F G) composed derivativeG
    apply of_derivative (hf.smooth.comp x (hg.of_le (by simp)))
    apply product.congr
    have nearF := Filter.Tendsto.eventually hg.continuousAt (hf.smooth.eventually (by simp))
    have nearG := (hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    filter_upwards [nearF,nearG] with y hyf hyg
    exact (fderiv_comp y (hyf.differentiableAt (by simp))
      (hyg.differentiableAt (by simp))).symm

end LeanShared.FractionalManifoldRegularity.JetAt
