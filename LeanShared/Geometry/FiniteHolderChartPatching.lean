module
public import LeanShared.Geometry.SupportedHolderChartSpace
public import LeanShared.Geometry.FractionalHolderAddition
public import LeanShared.Geometry.SmoothFractionalRegularity

/-! Actual finite-chart Hölder reconstruction. The map is the literal
sum of inverse-chart zero extensions, with a proved finite uniform norm
bound, support control and fractional regularity on every completed
coordinate vector. -/
public noncomputable section
open Set IsManifold
open scoped BigOperators Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.FiniteHolderChartPatching
variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [Fintype I]
  (a : ℝ) (K : I → Set E) (compact : ∀ i, IsCompact (K i))
  (e : I → OpenPartialHomeomorph M E) (target : ∀ i, K i ⊆ (e i).target)

local instance graphSeminormed : SeminormedAddCommGroup (BoundedHolderSpace.graph E a) :=
  (inferInstance : NormedAddCommGroup (BoundedHolderSpace.graph E a)).toSeminormedAddCommGroup

local instance supportedSeminormed (i : I) :
    SeminormedAddCommGroup (SupportedHolderChartSpace.space (a := a) (K i)) :=
  (inferInstance : NormedAddCommGroup (SupportedHolderChartSpace.space (a := a) (K i))).toSeminormedAddCommGroup

@[expose] def reconstruction :
    (∀ i, SupportedHolderChartSpace.space (a := a) (K i)) →L[ℂ] (M →ᵇ ℂ) :=
  ∑ i, (SupportedHolderChartSpace.realization (compact i) (e i) (target i)).comp
    (ContinuousLinearMap.proj i)

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem reconstruction_apply (v : ∀ i, SupportedHolderChartSpace.space (a := a) (K i)) (x : M) :
    reconstruction a K compact e target v x =
      ∑ i, SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i) x := by
  simp only [reconstruction, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, BoundedContinuousFunction.sum_apply]

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem norm_reconstruction (v : ∀ i, SupportedHolderChartSpace.space (a := a) (K i)) :
    ‖reconstruction a K compact e target v‖ ≤ (Fintype.card I : ℝ) * ‖v‖ := by
  have identity : reconstruction a K compact e target v =
      ∑ i, SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i) := by
    ext x
    simpa only [BoundedContinuousFunction.sum_apply] using reconstruction_apply a K compact e target v x
  rw [identity]
  calc
    _ ≤ ∑ i, ‖SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : I, ‖v‖ := Finset.sum_le_sum (fun i _ =>
      (by
        have bound := (SupportedHolderChartSpace.realization (compact i) (e i) (target i)).le_opNorm (v i)
        have bound' := bound.trans (mul_le_mul_of_nonneg_right
          (SupportedHolderChartSpace.realization_norm (a := a) (compact i) (e i) (target i)) (norm_nonneg (v i)))
        have estimate : ‖SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i)‖ ≤ ‖v i‖ := by
          simpa only [one_mul] using bound'
        exact estimate.trans (norm_le_pi_norm v i)))
    _ = _ := by simp

omit [NormedSpace ℝ E] [ChartedSpace E M] in
theorem reconstruction_support (v : ∀ i, SupportedHolderChartSpace.space (a := a) (K i)) :
    tsupport (fun x => reconstruction a K compact e target v x) ⊆
      ⋃ i, (e i).symm '' K i := by
  have identity : (fun x => reconstruction a K compact e target v x) =
      ∑ i, (fun x => SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i) x) := by
    funext x
    simpa only [Finset.sum_apply] using reconstruction_apply a K compact e target v x
  rw [identity]
  apply closure_minimal
  · intro x hx
    by_contra hn
    apply hx
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply image_eq_zero_of_notMem_tsupport
    intro hi
    exact hn (mem_iUnion.mpr ⟨i,
      SupportedHolderChartSpace.realization_support (compact i) (e i) (target i) (v i) hi⟩)
  · apply isClosed_iUnion_of_finite
    intro i
    exact ((compact i).image_of_continuousOn ((e i).symm.continuousOn.mono (target i))).isClosed

theorem reconstruction_regular [IsManifold (𝓘(ℝ,E)) ∞ M]
    (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (ha : 0 < a) (ha1 : a < 1)
    (v : ∀ i, SupportedHolderChartSpace.space (a := a) (K i)) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
      (fun x => reconstruction a K compact e target v x) := by
  have regular_sum (s : Finset I) :
      FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a
        (fun x => ∑ i ∈ s, SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i) x) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simpa using FractionalManifoldRegularity.regular_of_smooth
        (contMDiff_const (c := (0 : ℂ))) ha.le
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact FractionalManifoldRegularity.add_of_order_lt_one ha ha1
        (SupportedHolderChartSpace.realization_regular (compact i) (e i) (target i)
          (atlas i) ha ha1 (v i)) ih
  have identity : (fun x => reconstruction a K compact e target v x) =
      (fun x => ∑ i : I, SupportedHolderChartSpace.realization (compact i) (e i) (target i) (v i) x) :=
    funext (reconstruction_apply a K compact e target v)
  rw [identity]
  exact regular_sum Finset.univ
end LeanShared.FiniteHolderChartPatching
