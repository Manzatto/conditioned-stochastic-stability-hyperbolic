module
public import LeanShared.Geometry.ChartHolderTransport
public import LeanShared.Geometry.ManifoldSmoothHolderCore
public import LeanShared.Geometry.EuclideanLittleChartExtension

/-! Actual bounded coordinate maps between all chartwise little-Hölder
spaces of the constructed atlas. Literal cutoff/chart formulas and smooth
core compatibility are proved, not supplied. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldHolderCoordinateOperators
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0<b) (hb1 : b<1)

abbrev regions := ManifoldSmoothHolderCore.regions e D openV
abbrev Local (i : D.indices) := EuclideanSmoothHolderCore.space ((regions e D openV).compact_closure i) hb hb1

structure Transport (i j : D.indices) where
  map : Local e D openV hb hb1 j →L[ℂ] Local e D openV hb hb1 i
  physical : ∀v y, EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1 (map v) y =
    ChartLocalization.coordinate (e i) (D.cutoff i)
      (SupportedChartExtension.function (e j)
        (EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure j) hb hb1 v)) y
  smooth : ∀c, map (EuclideanSmoothHolderCore.smooth ((regions e D openV).compact_closure j) hb hb1 c) =
    EuclideanSmoothHolderCore.smooth ((regions e D openV).compact_closure i) hb hb1
      (ManifoldSmoothHolderCore.localCore e D atlas openV i
        (ManifoldSmoothHolderCore.extendCore e D atlas openV j c))

include atlas in
theorem exists_transport (i j : D.indices) : Nonempty (Transport e D atlas openV hb hb1 i j) := by
  let r := regions e D openV
  obtain ⟨T,formula⟩ := ChartHolderTransport.exists_transport (e i) (e j) (atlas i) (atlas j)
    (D.cutoff i) (D.smooth i) (D.compact i) (D.support i)
    (r.compact_closure j) (r.closure_target j) hb.le hb1.le
  let raw := T.comp (EuclideanSmoothHolderCore.space (r.compact_closure j) hb hb1).subtypeL
  have coreEq (c : SmoothSupportedManifoldCore.core (E:=E) (r.region j)) :
      raw (EuclideanSmoothHolderCore.smooth (r.compact_closure j) hb hb1 c) =
      EuclideanSmoothHolderCore.core (r.compact_closure i) hb hb1
        (ManifoldSmoothHolderCore.localCore e D atlas openV i
          (ManifoldSmoothHolderCore.extendCore e D atlas openV j c)) := by
    apply BoundedHolderSpace.physical_injective E b
    ext y
    have statement := formula (EuclideanSmoothHolderCore.core (r.compact_closure j) hb hb1 c)
      (fun z hz => SmoothSupportedManifoldCore.zero_outside (r.region j) c z
        (fun hs => hz (subset_closure hs))) y
    exact statement
  have maps (v : Local e D openV hb hb1 j) : raw v∈EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1 := by
    apply (EuclideanSmoothHolderCore.smooth_dense (r.compact_closure j) hb hb1).induction_on
      (p:=fun z => raw z∈EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1) v
      (((EuclideanSmoothHolderCore.core (r.compact_closure i) hb hb1).range.isClosed_topologicalClosure).preimage raw.continuous)
    intro c
    rw [coreEq]
    exact (EuclideanSmoothHolderCore.core (r.compact_closure i) hb hb1).range.le_topologicalClosure ⟨_,rfl⟩
  let result := raw.codRestrict (EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1) maps
  refine ⟨⟨result,?_,?_⟩⟩
  · intro v y
    exact formula v.val
      (fun z hz => EuclideanLittleChartExtension.zero_outside_closure (r.compact_closure j) hb hb1 v z hz) y
  · intro c
    exact Subtype.ext (coreEq c)
end LeanShared.ManifoldHolderCoordinateOperators
