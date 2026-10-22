module
public import LeanShared.Geometry.CompactRiemannianTrivializations
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity

/-! Uniform equivalence of two actual continuous Riemannian metrics on a
compact base. Norms are named explicitly to preserve the original fiber
topology and avoid silently changing a metric instance in a bound. -/
public noncomputable section
open Set Filter Bundle
open scoped Topology BigOperators
namespace LeanShared.CompactRiemannianMetricComparison
variable {B F : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, IsTopologicalAddGroup (E x)]
  [∀ x, ContinuousConstSMul ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

@[expose] def fiberNorm (g : RiemannianMetric E) (x : B) (v : E x) : ℝ :=
  Real.sqrt (g.inner x v v)

omit [TopologicalSpace B] in
theorem norm_eq_fiberNorm (g : RiemannianMetric E) (x : B) (v : E x) :
    letI : RiemannianBundle E := ⟨g⟩;
    ‖v‖ = fiberNorm E g x v := by
  let : RiemannianBundle E := ⟨g⟩
  exact norm_eq_sqrt_real_inner v

/-- Recover the actual continuous metric data from the genuine continuity
class, rather than assuming another reference metric. -/
@[expose] def continuousMetricOfBundle [RiemannianBundle E]
    [IsContinuousRiemannianBundle F E] : ContinuousRiemannianMetric F E where
  inner := RiemannianBundle.g.inner
  symm := RiemannianBundle.g.symm
  pos := RiemannianBundle.g.pos
  isVonNBounded := RiemannianBundle.g.isVonNBounded
  continuous := by
    obtain ⟨g, continuous, represents⟩ := IsContinuousRiemannianBundle.exists_continuous (F := F) (E := E)
    apply continuous.congr
    intro x
    congr 1
    ext v w
    exact (represents x v w).symm

/-- Coordinate bounds expressed in the named actual metric norm. -/
theorem local_coordinates (g : ContinuousRiemannianMetric F E) (x : B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x,
      y ∈ (trivializationAt F E x).baseSet ∧
      (∀ v : E y, ‖(trivializationAt F E x).continuousLinearMapAt ℝ y v‖ ≤
        C * fiberNorm E g.toRiemannianMetric y v) ∧
      (∀ w : F, fiberNorm E g.toRiemannianMetric y
        ((trivializationAt F E x).symmL ℝ y w) ≤ C * ‖w‖) := by
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  obtain ⟨C, positiveC, bounds⟩ := CompactRiemannianTrivializations.local_bound (F := F) E x
  refine ⟨C, positiveC, ?_⟩
  filter_upwards [bounds] with y hy
  refine ⟨hy.1, ?_, ?_⟩
  · intro v
    rw [← norm_eq_fiberNorm E g.toRiemannianMetric y v]
    exact ((trivializationAt F E x).continuousLinearMapAt ℝ y).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hy.2.1 (norm_nonneg _))
  · intro w
    rw [← norm_eq_fiberNorm E g.toRiemannianMetric y
      ((trivializationAt F E x).symmL ℝ y w)]
    exact ((trivializationAt F E x).symmL ℝ y).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right hy.2.2 (norm_nonneg _))

theorem local_comparison (g₁ g₂ : ContinuousRiemannianMetric F E) (x : B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, ∀ v : E y,
      fiberNorm E g₂.toRiemannianMetric y v ≤ C * fiberNorm E g₁.toRiemannianMetric y v ∧
      fiberNorm E g₁.toRiemannianMetric y v ≤ C * fiberNorm E g₂.toRiemannianMetric y v := by
  obtain ⟨C₁, positive₁, bounds₁⟩ := local_coordinates E g₁ x
  obtain ⟨C₂, positive₂, bounds₂⟩ := local_coordinates E g₂ x
  refine ⟨C₁ * C₂, mul_pos positive₁ positive₂, ?_⟩
  filter_upwards [bounds₁, bounds₂] with y h₁ h₂
  intro v
  let e := trivializationAt F E x
  have reconstruct : e.symmL ℝ y (e.continuousLinearMapAt ℝ y v) = v :=
    e.symmL_continuousLinearMapAt h₁.1 v
  constructor
  · calc
      _ = fiberNorm E g₂.toRiemannianMetric y
          (e.symmL ℝ y (e.continuousLinearMapAt ℝ y v)) := congrArg _ reconstruct.symm
      _ ≤ C₂ * ‖e.continuousLinearMapAt ℝ y v‖ := h₂.2.2 _
      _ ≤ C₂ * (C₁ * fiberNorm E g₁.toRiemannianMetric y v) :=
        mul_le_mul_of_nonneg_left (h₁.2.1 v) positive₂.le
      _ = _ := by ring
  · calc
      _ = fiberNorm E g₁.toRiemannianMetric y
          (e.symmL ℝ y (e.continuousLinearMapAt ℝ y v)) := congrArg _ reconstruct.symm
      _ ≤ C₁ * ‖e.continuousLinearMapAt ℝ y v‖ := h₁.2.2 _
      _ ≤ C₁ * (C₂ * fiberNorm E g₂.toRiemannianMetric y v) :=
        mul_le_mul_of_nonneg_left (h₂.2.1 v) positive₁.le
      _ = _ := by ring

/-- A single positive constant compares both actual norms everywhere on the
compact set. The original and replacement metric remain separately named. -/
theorem uniform_comparison (g₁ g₂ : ContinuousRiemannianMetric F E)
    (K : Set B) (compact : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : E x,
      fiberNorm E g₂.toRiemannianMetric x v ≤ C * fiberNorm E g₁.toRiemannianMetric x v ∧
      fiberNorm E g₁.toRiemannianMetric x v ≤ C * fiberNorm E g₂.toRiemannianMetric x v := by
  classical
  choose c positive neighborhoods using local_comparison E g₁ g₂
  have opens (x : B) : ∃ U : Set B, U ⊆ {y | ∀ v : E y,
      fiberNorm E g₂.toRiemannianMetric y v ≤ c x * fiberNorm E g₁.toRiemannianMetric y v ∧
      fiberNorm E g₁.toRiemannianMetric y v ≤ c x * fiberNorm E g₂.toRiemannianMetric y v} ∧
      IsOpen U ∧ x ∈ U := mem_nhds_iff.mp (neighborhoods x)
  choose U subset openU member using opens
  obtain ⟨centers, covers⟩ := compact.elim_finite_subcover U openU
    (fun x _ => mem_iUnion.mpr ⟨x, member x⟩)
  let C := 1 + ∑ x ∈ centers, c x
  have positiveC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun x _ => (positive x).le))
  refine ⟨C, positiveC, ?_⟩
  intro x hx v
  obtain ⟨y, hy, member⟩ := mem_iUnion₂.mp (covers hx)
  have bound : c y ≤ C :=
    (Finset.single_le_sum (fun j _ => (positive j).le) hy).trans
      (le_add_of_nonneg_left zero_le_one)
  have estimates := subset y member v
  exact ⟨estimates.1.trans (mul_le_mul_of_nonneg_right bound (Real.sqrt_nonneg _)),
    estimates.2.trans (mul_le_mul_of_nonneg_right bound (Real.sqrt_nonneg _))⟩

end LeanShared.CompactRiemannianMetricComparison
