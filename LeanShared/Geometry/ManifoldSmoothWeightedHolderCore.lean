module
public import LeanShared.Geometry.ManifoldRoughHolderRealization
public import LeanShared.Geometry.FractionalRegularProduct

/-! A literal finite-regular weighted composition of a supported smooth
input belongs to the actually constructed manifold little-Hölder space.
Fractional weights and merely C¹ maps suffice. -/
public noncomputable section
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldSmoothHolderCore
variable {E M J:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μ:Measure E) [μ.IsAddHaarMeasure] {V S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M) (openV:IsOpen V) (region:V⊆S)
  {b u:ℝ} (hb:0<b) (hb1:b<1) (hbu:b<u) (hu1:u<1)
  {w:M→ℂ} (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
  (support:tsupport w⊆V) (F:M→M) (hF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)

include μ atlas region hbu hu1 hw support hF in
omit [CompactSpace M] in
theorem exists_weighted_core_lower (c:SmoothSupportedManifoldCore.core (E:=E) V) :
    ∃v:Lower e D openV hb hb1,∀x:M,physical e D openV hb hb1 v x=w x*c.val (F x) := by
  have regular : FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u (fun x=>w x*c.val (F x)) :=
    FractionalManifoldRegularity.mul_contMDiff_one (hb.trans hbu) hu1 hw
      ((c.property.1.of_le (by simp)).comp hF)
  let rough : RoughFunctions (E:=E) u V :=
    ⟨fun x=>w x*c.val (F x),regular,tsupport_mul_subset_left.trans support⟩
  exact ⟨lower μ e D atlas openV hb hb1 hbu rough,
    fun x=>physical_lower μ e D atlas openV region hb hb1 hbu rough x⟩
end LeanShared.ManifoldSmoothHolderCore
