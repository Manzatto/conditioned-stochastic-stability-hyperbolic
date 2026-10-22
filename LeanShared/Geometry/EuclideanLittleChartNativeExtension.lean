module
public import LeanShared.Geometry.SupportedHolderChartNativeMap
public import LeanShared.Geometry.EuclideanLittleChartExtension
public import LeanShared.Geometry.BoundedRiemannianSmoothHolderCore
public import LeanShared.Geometry.SmoothHolderTestSpaces

/-! Genuine preservation of the smooth-core closure by chart extension.
The source is the actual Euclidean little Holder completion; the target is
its native bounded-Riemannian counterpart. -/
public noncomputable section
namespace LeanShared.EuclideanLittleChartExtension
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    {W : Set E} (compact : IsCompact (closure W))
    (e : OpenPartialHomeomorph M E) (inside : closure W ⊆ e.target)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)


/-- The chart map is bounded in the actual native graph norm. -/
def nativeGraph :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    EuclideanSmoothHolderCore.space compact hb hb1 →L[ℂ] BoundedHolderSpace.graph M b := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact (SupportedHolderChartSpace.nativeRealization hb.le compact e inside he).comp
    (supported compact hb hb1)

theorem nativeGraph_physical (v : EuclideanSmoothHolderCore.space compact hb hb1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    BoundedHolderSpace.physical M b (nativeGraph hb hb1 compact e inside he v) =
      realization compact hb hb1 e inside v :=
  SupportedHolderChartSpace.physical_nativeRealization hb.le compact e inside he _

/-- A supported smooth coordinate function extends as a genuine manifold
smooth function with support in the specified region. -/
def extendedSmooth {V : Set M} (region : e.symm '' W ⊆ V)
    (c : SmoothSupportedManifoldCore.core (E := E) W) :
    SmoothSupportedManifoldCore.core (E := E) V :=
  ⟨SupportedChartExtension.function e c.val,
    SupportedChartExtension.smooth e he c.property.1.contDiff
      (EuclideanSmoothHolderCore.compact_support compact c)
      (c.property.2.trans (subset_closure.trans inside)),
    (SupportedChartExtension.support_subset e
      (EuclideanSmoothHolderCore.compact_support compact c)
      (c.property.2.trans (subset_closure.trans inside))).trans
      ((image_mono c.property.2).trans region)⟩

/-- Little-space preservation is a consequence of smooth-core density and
closedness, rather than an extra membership premise. -/
theorem nativeGraph_mem {V : Set M} (region : e.symm '' W ⊆ V)
    (v : EuclideanSmoothHolderCore.space compact hb hb1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    nativeGraph hb hb1 compact e inside he v ∈ SmoothHolderTestSpaces.space b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  apply (EuclideanSmoothHolderCore.smooth_dense compact hb hb1).induction_on
    (p := fun z => nativeGraph hb hb1 compact e inside he z ∈ SmoothHolderTestSpaces.space b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V) v
    (((SmoothHolderTestSpaces.holderCore b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V).range.isClosed_topologicalClosure).preimage
      (nativeGraph hb hb1 compact e inside he).continuous)
  intro c
  apply (SmoothHolderTestSpaces.holderCore b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V).range.le_topologicalClosure
  refine ⟨extendedSmooth compact e inside he region c, ?_⟩
  apply BoundedHolderSpace.physical_injective M b
  rw [nativeGraph_physical]
  ext x
  rfl

/-- The resulting map between the two actual little completions. -/
def nativeExtension {V : Set M} (region : e.symm '' W ⊆ V) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    EuclideanSmoothHolderCore.space compact hb hb1 →L[ℂ]
      SmoothHolderTestSpaces.space b
        (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact (nativeGraph hb hb1 compact e inside he).codRestrict _
    (nativeGraph_mem hb hb1 compact e inside he region)

end LeanShared.EuclideanLittleChartExtension
