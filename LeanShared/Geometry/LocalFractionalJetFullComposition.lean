module
public import LeanShared.Geometry.LocalFractionalJetComposition

/-! Genuine Holder-jet composition for a smooth outer map, and for two fractionally regular maps
when the inner map is C1. Both rules are proved by the actual derivative chain rule and the
bilinear jet rule. -/
public noncomputable section
namespace LeanShared.FractionalManifoldRegularity.JetAt
open Set Filter
open scoped Topology ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 3200000 in
theorem smooth_comp (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ {F G : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} {g : E → F} {x : E},
      ContDiffAt ℝ ∞ f (g x) → JetAt n a g x → JetAt n a (f ∘ g) x := by
  induction n with
  | zero =>
    intro F G _ _ _ _ f g x hf hg
    obtain ⟨U, openU, inU, C, hC, bound⟩ := hg.holder
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] at bound
    obtain ⟨L, V, nearV, lip⟩ := (hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
    obtain ⟨W, subW, openW, inW⟩ := mem_nhds_iff.mp
      (inter_mem (openU.mem_nhds inU) (hg.smooth.continuousAt.preimage_mem_nhds nearV))
    refine ⟨(hf.of_le (by simp)).comp x hg.smooth, W, openW, inW,
      (L : ℝ) * C, mul_nonneg L.coe_nonneg hC, ?_⟩
    intro y hy z hz
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map]
    calc
      ‖f (g y) - f (g z)‖ ≤ (L : ℝ) * ‖g y-g z‖ := by
        simpa only [dist_eq_norm] using lip.dist_le_mul (g y) (subW hy).2 (g z) (subW hz).2
      _ ≤ (L : ℝ) * (C * ‖y-z‖^a) :=
        mul_le_mul_of_nonneg_left (bound y (subW hy).1 z (subW hz).1) L.coe_nonneg
      _ = _ := by ring
  | succ n ih =>
    intro F G _ _ _ _ f g x hf hg
    have composed := ih (hf.fderiv_right (by simp)) (of_contDiff_succ ha1 hg.smooth)
    have product := bilinear n ha ha1 (ContinuousLinearMap.compL ℝ E F G) composed hg.derivative
    apply of_derivative ((hf.of_le (by simp)).comp x hg.smooth)
    apply product.congr
    have nearF := hg.smooth.continuousAt.eventually
      ((hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num))
    have nearG := hg.smooth.eventually (by simp)
    filter_upwards [nearF, nearG] with y hyf hyg
    exact (fderiv_comp y (hyf.differentiableAt (by simp))
      (hyg.differentiableAt (by simp))).symm

set_option maxHeartbeats 3200000 in
theorem comp_of_c1_inner (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ∀ {F G : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] {f : F → G} {g : E → F} {x : E},
      JetAt n a f (g x) → JetAt n a g x → ContDiffAt ℝ 1 g x → JetAt n a (f ∘ g) x := by
  induction n with
  | zero =>
    intro F G _ _ _ _ f g x hf hg hg1
    obtain ⟨U, openU, inU, C, hC, boundF⟩ := hf.holder
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] at boundF
    obtain ⟨W, openW, inW, _maps, A, hA, bound⟩ :=
      LocalHolderComposition.exists_bound ha hC hg1 (openU.mem_nhds inU) boundF
    refine ⟨hf.smooth.comp x hg.smooth, W, openW, inW, A, hA, ?_⟩
    intro y hy z hz
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
      LinearIsometryEquiv.norm_map] using bound y hy z hz
  | succ n ih =>
    intro F G _ _ _ _ f g x hf hg hg1
    have composed := ih hf.derivative (of_contDiff_succ ha1 hg.smooth) hg1
    have product := bilinear n ha ha1 (ContinuousLinearMap.compL ℝ E F G) composed hg.derivative
    apply of_derivative (hf.smooth.comp x hg.smooth)
    apply product.congr
    have nearF := hg1.continuousAt.eventually (hf.smooth.eventually (by simp))
    have nearG := hg.smooth.eventually (by simp)
    filter_upwards [nearF, nearG] with y hyf hyg
    exact (fderiv_comp y (hyf.differentiableAt (by simp))
      (hyg.differentiableAt (by simp))).symm

end LeanShared.FractionalManifoldRegularity.JetAt
