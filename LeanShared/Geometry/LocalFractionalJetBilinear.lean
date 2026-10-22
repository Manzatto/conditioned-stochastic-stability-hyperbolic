module
public import LeanShared.Geometry.LocalFractionalJetAddition
public import LeanShared.Analysis.LocalHolderBilinear
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-! A genuine all-order fractional product rule. The induction uses actual
Fréchet derivative identities and bounded bilinear maps, not a supplied
fractional calculus or higher jet estimate. -/
public noncomputable section
namespace LeanShared.FractionalManifoldRegularity.JetAt
open Set Filter
open scoped Topology ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 3200000 in
theorem bilinear (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ {F G H : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
      (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G} {x : E},
      JetAt n a f x → JetAt n a g x → JetAt n a (fun y => B (f y) (g y)) x := by
  induction n with
  | zero =>
    intro F G H _ _ _ _ _ _ B f g x hf hg
    obtain ⟨U,openU,inU,C,hC,boundF⟩ := hf.holder
    obtain ⟨V,openV,inV,D,hD,boundG⟩ := hg.holder
    simp only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,
      LinearIsometryEquiv.norm_map] at boundF boundG
    obtain ⟨W,openW,inW,_inside,A,hA,bound⟩ := LocalHolderBilinear.exists_bound B ha hC hD
      (openU.mem_nhds inU) (openV.mem_nhds inV) boundF boundG
    refine ⟨(B.contDiff.contDiffAt.comp x hf.smooth).clm_apply hg.smooth,
      W,openW,inW,A,hA,?_⟩
    intro y hy z hz
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,←map_sub,
      LinearIsometryEquiv.norm_map] using bound y hy z hz
  | succ n ih =>
    intro F G H _ _ _ _ _ _ B f g x hf hg
    have right := ih (B.precompR E) (of_contDiff_succ ha1 hf.smooth) hg.derivative
    have left := ih (B.precompL E) hf.derivative (of_contDiff_succ ha1 hg.smooth)
    have smooth := (B.contDiff.contDiffAt.comp x hf.smooth).clm_apply hg.smooth
    apply of_derivative smooth
    apply (right.add left).congr
    filter_upwards [hf.smooth.eventually (by simp),hg.smooth.eventually (by simp)] with y hyf hyg
    exact (B.fderiv_of_bilinear (hyf.differentiableAt (by simp))
      (hyg.differentiableAt (by simp))).symm

end LeanShared.FractionalManifoldRegularity.JetAt
