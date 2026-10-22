module
public import LeanShared.Geometry.ManifoldHolderNativeMembership
import all LeanShared.Geometry.EuclideanLittleChartNativeExtension

/-! The bounded inclusion of the constructed lower-regularity manifold space
(chart coordinates modulo the reconstruction kernel) into the native little
Hölder space of the constructed Riemannian length metric: sum the chartwise
native extensions; their physical function is the literal reconstruction, so
the reconstruction kernel lies in the kernel and the sum descends to the
quotient. The inclusion preserves the physical functions. -/
public noncomputable section
namespace LeanShared.ManifoldHolderQuotient
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle BoundedContinuousFunction BigOperators

variable {E M I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T3Space M] [CompactSpace M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [Fintype I] {e : I → OpenPartialHomeomorph M E} {K : I → Set E} {V : Set M}
    (d : ChartSmoothingRegions.Data e K V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)

local instance coordinatesNormedNative : NormedAddCommGroup (Coordinates d hb hb1) := inferInstance
local instance coordinatesSeminormedNative : SeminormedAddCommGroup (Coordinates d hb hb1) :=
  (coordinatesNormedNative d hb hb1).toSeminormedAddCommGroup
local instance coordinatesScalarNative : NormedSpace ℂ (Coordinates d hb hb1) := inferInstance

/-- The sum of the chartwise native extensions. -/
def nativeCoordinates :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    Coordinates d hb hb1 →L[ℂ] SmoothHolderTestSpaces.space b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact ∑ i, (EuclideanLittleChartExtension.nativeExtension hb hb1
    (d.compact_closure i) (e i) (d.closure_target i) (atlas i)
    (by rintro _ ⟨y,hy,rfl⟩; exact d.inverse_region i y hy)).comp (ContinuousLinearMap.proj i)

set_option maxHeartbeats 1600000 in
theorem physical_nativeCoordinates (c : Coordinates d hb hb1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    SmoothHolderTestSpaces.physical b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V
      (nativeCoordinates d hb hb1 atlas c) = reconstruction d hb hb1 c := by
  classical
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  change SmoothHolderTestSpaces.physical b _ V
    ((∑ i, (EuclideanLittleChartExtension.nativeExtension hb hb1
      (d.compact_closure i) (e i) (d.closure_target i) (atlas i)
      (by rintro _ ⟨y,hy,rfl⟩; exact d.inverse_region i y hy)).comp
        (ContinuousLinearMap.proj i)) c) = _
  rw [sum_apply, map_sum]
  ext x
  rw [BoundedContinuousFunction.sum_apply]
  change (∑ i, SmoothHolderTestSpaces.physical b _ V
      (EuclideanLittleChartExtension.nativeExtension hb hb1
      (d.compact_closure i) (e i) (d.closure_target i) (atlas i)
      (by rintro _ ⟨y,hy,rfl⟩; exact d.inverse_region i y hy) (c i)) x) =
    FiniteHolderChartPatching.reconstruction b (fun i => closure (d.region i))
      d.compact_closure e d.closure_target (supportedCoordinates d hb hb1 c) x
  rw [FiniteHolderChartPatching.reconstruction_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold EuclideanLittleChartExtension.nativeExtension
  change BoundedHolderSpace.physical M b
    (EuclideanLittleChartExtension.nativeGraph hb hb1 (d.compact_closure i)
      (e i) (d.closure_target i) (atlas i) (c i)) x = _
  rw [EuclideanLittleChartExtension.nativeGraph_physical]
  rfl

theorem kernel_le :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    (reconstruction d hb hb1).ker ≤ (nativeCoordinates d hb hb1 atlas).ker := by
  intro _ c hc
  change nativeCoordinates d hb hb1 atlas c = 0
  apply SmoothHolderTestSpaces.physical_injective b
    (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V
  rw [physical_nativeCoordinates d hb hb1 atlas c, map_zero]
  exact hc

/-- The bounded inclusion of the lower-regularity space into the native little Hölder space. -/
def nativeInclusion :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    Space d hb hb1 →L[ℂ] SmoothHolderTestSpaces.space b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  exact (reconstruction d hb hb1).ker.liftQL (nativeCoordinates d hb hb1 atlas)
    (kernel_le d hb hb1 atlas)

theorem physical_nativeInclusion (v : Space d hb hb1) :
    let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
    SmoothHolderTestSpaces.physical b
      (BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b hb1.le) V
      (nativeInclusion d hb hb1 atlas v) = physical d hb hb1 v := by
  let _ : MetricSpace M := BoundedRiemannianMetric.metric (E := E)
  obtain ⟨c, rfl⟩ := BanachFunctionQuotient.quotient_surjective (𝕜 := ℂ)
    (H := Coordinates d hb hb1) (X := M) (F := ℂ) (reconstruction d hb hb1) v
  exact (physical_nativeCoordinates d hb hb1 atlas c).trans
    (BanachFunctionQuotient.physical_quotient (𝕜 := ℂ) (H := Coordinates d hb hb1) (X := M)
      (F := ℂ) _ c).symm

end LeanShared.ManifoldHolderQuotient
