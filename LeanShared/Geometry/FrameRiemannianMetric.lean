module

public import LeanShared.Geometry.BilinearBundleContinuity
public import Mathlib.Analysis.LocallyConvex.Bounded

/-! A compatible continuous Riemannian metric from an actual continuous
coframe. Fiber norms are constructed from the frame and the original
fiber topology, rather than assumed as extra geometric data. -/

@[expose] public noncomputable section
open Set Bundle
open scoped Bundle Topology
namespace LeanShared.FrameRiemannianMetric
variable {B H F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {E : B → Type*} [∀ x, TopologicalSpace (E x)]
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousConstSMul ℝ (E x)]
  [TopologicalSpace (TotalSpace H E)] [FiberBundle H E] [VectorBundle ℝ H E]
  (frame : ∀ x, F ≃L[ℝ] E x)

def form (x : B) : E x →L[ℝ] E x →L[ℝ] ℝ :=
  ((frame x).arrowCongr ((frame x).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))) (innerSL ℝ)

omit [TopologicalSpace B] [∀ x, IsTopologicalAddGroup (E x)]
  [∀ x, ContinuousConstSMul ℝ (E x)] in
@[simp] theorem form_apply (x : B) (v w : E x) :
    form frame x v w = inner ℝ ((frame x).symm v) ((frame x).symm w) := rfl

def metric : RiemannianMetric E where
  inner := form frame
  symm x v w := real_inner_comm _ _
  pos x v hv := by
    rw [form_apply, real_inner_self_pos]
    exact fun zero => hv ((frame x).symm.injective (zero.trans (map_zero _).symm))
  continuousAt x := by
    exact (((frame x).symm.continuous.inner (frame x).symm.continuous)).continuousAt
  isVonNBounded x := by
    apply ((NormedSpace.isVonNBounded_ball ℝ F 1).image (frame x).toContinuousLinearMap).subset
    intro v hv
    refine ⟨(frame x).symm v, ?_, (frame x).apply_symm_apply v⟩
    rw [Metric.mem_ball, dist_zero_right]
    have square : ‖(frame x).symm v‖ ^ 2 < 1 := by
      simpa only [mem_ofPred_eq, form_apply, real_inner_self_eq_norm_sq] using hv
    nlinarith [norm_nonneg ((frame x).symm v)]

theorem continuous_form
    (coframe : Continuous (fun p : TotalSpace H E => (frame p.1).symm p.2)) :
    letI : RiemannianBundle E := ⟨metric frame⟩;
    Continuous (fun x => TotalSpace.mk' (H →L[ℝ] H →L[ℝ] ℝ) x (form frame x)) := by
  let : RiemannianBundle E := ⟨metric frame⟩
  apply BilinearBundleContinuity.of_pairings
  intro U v w hv hw
  simp only [form_apply]
  exact (coframe.comp_continuousOn hv).inner (coframe.comp_continuousOn hw)

omit [FiniteDimensional ℝ H] [∀ x, IsTopologicalAddGroup (E x)]
  [∀ x, ContinuousConstSMul ℝ (E x)] in
theorem continuous_frame [FiniteDimensional ℝ F]
    (sections : ∀ a : F, Continuous (fun x => (⟨x, frame x a⟩ : TotalSpace H E))) :
    Continuous (fun p : B × F => (⟨p.1, frame p.1 p.2⟩ : TotalSpace H E)) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨continuous_fst.continuousAt, ?_⟩
  let e := trivializationAt H E p.1
  have hx : p.1 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p.1
  have each (a : F) : ContinuousAt (fun x => e.continuousLinearMapAt ℝ x (frame x a)) p.1 := by
    have h := (sections a).continuousAt (x := p.1)
    rw [FiberBundle.continuousAt_totalSpace] at h
    apply h.2.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with x hx
    exact e.continuousLinearMapAt_apply_of_mem ℝ hx (frame x a)
  have maps : ContinuousAt (fun x => (e.continuousLinearMapAt ℝ x).comp (frame x).toContinuousLinearMap) p.1 :=
    continuousAt_clm_apply.mpr each
  have applyMap := (maps.comp continuous_fst.continuousAt).clm_apply continuous_snd.continuousAt
  apply applyMap.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)] with q hq
  exact (e.continuousLinearMapAt_apply_of_mem ℝ hq (frame q.1 q.2)).symm

end LeanShared.FrameRiemannianMetric
