module
public import LeanShared.Geometry.ChartWeightedHolderMapTransport
public import LeanShared.Geometry.ManifoldSmoothWeightedHolderCore
public import LeanShared.Geometry.EuclideanLittleChartExtension

/-! Literal finite-regular transfer coordinates between the constructed
little Hölder chart spaces. Membership follows from proved supported
smoothing and fractional product calculus; the norm bound is constructed
by the actual chart weighted-composition operator. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace LeanShared.ManifoldWeightedHolderCoordinateOperators
variable {E M J:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μ:Measure E) [μ.IsAddHaarMeasure] {S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V:Set M} (openV:IsOpen V) {u b:ℝ} (hb:0<b) (hb1:b<1)
  (hbu:b<u) (hu1:u<1) {w:M→ℂ}
  (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
  (support:tsupport w⊆V) (F:M→M) (hF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)

abbrev regions := ManifoldSmoothHolderCore.regions e D openV
abbrev Local (i:D.indices) := EuclideanSmoothHolderCore.space ((regions e D openV).compact_closure i) hb hb1

structure Transport (i j:D.indices) where
  map : Local e D openV hb hb1 j →L[ℂ] Local e D openV hb hb1 i
  physical : ∀v y,EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1 (map v) y=
    ChartLocalization.coordinate (e i) (D.cutoff i)
      (fun x=>w x*SupportedChartExtension.function (e j)
        (EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure j) hb hb1 v) (F x)) y

include μ atlas hbu hu1 hw support hF in
omit [CompactSpace M] in
theorem exists_transport (i j:D.indices) : Nonempty (Transport e D openV hb hb1 F (w:=w) i j) := by
  let r := regions e D openV
  obtain ⟨T,formula⟩ := ChartWeightedHolderMapTransport.exists_transport (e i) (e j) (atlas i) (atlas j)
    (D.cutoff i) (D.smooth i) (D.compact i) (D.support i)
    (r.compact_closure j) (r.closure_target j) F hF (hb.trans hbu) hu1 hw hb.le hbu
  let raw := T.comp (EuclideanSmoothHolderCore.space (r.compact_closure j) hb hb1).subtypeL
  have smooth_member (c:SmoothSupportedManifoldCore.core (E:=E) (r.region j)) :
      raw (EuclideanSmoothHolderCore.smooth (r.compact_closure j) hb hb1 c)∈
        EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1 := by
    let cM := ManifoldSmoothHolderCore.extendCore e D atlas openV j c
    have regular : FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u (fun x=>w x*cM.val (F x)) :=
      FractionalManifoldRegularity.mul_contMDiff_one (hb.trans hbu) hu1 hw
        ((cM.property.1.of_le (by simp)).comp hF)
    let rough : ManifoldSmoothHolderCore.RoughFunctions (E:=E) u V :=
      ⟨fun x=>w x*cM.val (F x),regular,tsupport_mul_subset_left.trans support⟩
    obtain ⟨v,hv⟩ := ManifoldSmoothHolderCore.rough_coordinate_exists μ e D atlas openV hb hb1 hbu rough i
    have eqn : raw (EuclideanSmoothHolderCore.smooth (r.compact_closure j) hb hb1 c)=v.val := by
      apply BoundedHolderSpace.physical_injective E b
      ext y
      have h := formula (EuclideanSmoothHolderCore.core (r.compact_closure j) hb hb1 c)
        (fun z hz=>SmoothSupportedManifoldCore.zero_outside (r.region j) c z
          (fun hs=>hz (subset_closure hs))) y
      have value := congrArg (fun f:E→ᵇℂ=>f y) hv
      exact h.trans value.symm
    exact eqn ▸ v.property
  have maps (v:Local e D openV hb hb1 j) : raw v∈EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1 := by
    apply (EuclideanSmoothHolderCore.smooth_dense (r.compact_closure j) hb hb1).induction_on
      (p:=fun z=>raw z∈EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1) v
      (((EuclideanSmoothHolderCore.core (r.compact_closure i) hb hb1).range.isClosed_topologicalClosure).preimage raw.continuous)
    exact smooth_member
  let result := raw.codRestrict (EuclideanSmoothHolderCore.space (r.compact_closure i) hb hb1) maps
  refine ⟨⟨result,?_⟩⟩
  intro v y
  exact formula v.val
    (fun z hz=>EuclideanLittleChartExtension.zero_outside_closure (r.compact_closure j) hb hb1 v z hz) y
end LeanShared.ManifoldWeightedHolderCoordinateOperators
