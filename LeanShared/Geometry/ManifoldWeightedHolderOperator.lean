module
public import LeanShared.Geometry.ManifoldWeightedHolderCoordinateOperators
public import LeanShared.Geometry.ManifoldHolderLocalizationOperators
public import LeanShared.Geometry.ChartPartitionReconstruction

/-! The literal finite-regular transfer is a constructed bounded operator
on the actual chart-quotient little Hölder space. Its whole-space function
identity is proved by quotient descent, not supplied as an invariant-core
or finite-regular action source. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction BigOperators
namespace LeanShared.ManifoldWeightedHolderOperator
open ManifoldWeightedHolderCoordinateOperators
variable {E M J:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μ:Measure E) [μ.IsAddHaarMeasure] {S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V:Set M} (openV:IsOpen V) (region:V⊆S) {u b:ℝ} (hb:0<b) (hb1:b<1)
  (hbu:b<u) (hu1:u<1) {w:M→ℂ}
  (hw:FractionalManifoldRegularity.Regular (E:=E) (F:=ℂ) u w)
  (support:tsupport w⊆V) (F:M→M) (hF:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 F)

abbrev Coordinates := ManifoldHolderQuotient.Coordinates (regions e D openV) hb hb1
abbrev Regular := ManifoldSmoothHolderCore.Lower e D openV hb hb1
local instance coordinateNormed : NormedAddCommGroup (Coordinates e D openV hb hb1) := inferInstance
local instance coordinateSemi : SeminormedAddCommGroup (Coordinates e D openV hb hb1) :=
  (coordinateNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance coordinateScalar : NormedSpace ℂ (Coordinates e D openV hb hb1) := inferInstance
local instance regularNormed : NormedAddCommGroup (Regular e D openV hb hb1) := inferInstance
local instance regularSemi : SeminormedAddCommGroup (Regular e D openV hb hb1) :=
  (regularNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance regularScalar : NormedSpace ℂ (Regular e D openV hb hb1) := inferInstance
local instance localNormed (i:D.indices) : NormedAddCommGroup (Local e D openV hb hb1 i) := inferInstance
local instance localSemi (i:D.indices) : SeminormedAddCommGroup (Local e D openV hb hb1 i) :=
  (localNormed e D openV hb hb1 i).toSeminormedAddCommGroup
local instance localScalar (i:D.indices) : NormedSpace ℂ (Local e D openV hb hb1 i) := inferInstance

@[expose] def transport (i j:D.indices) : Transport e D openV hb hb1 F (w:=w) i j :=
  Classical.choice (exists_transport μ e D atlas openV hb hb1 hbu hu1 hw support F hF i j)

@[expose] def row (i:D.indices) : Coordinates e D openV hb hb1 →L[ℂ] Local e D openV hb hb1 i :=
  ∑j:D.indices,(transport μ e D atlas openV hb hb1 hbu hu1 hw support F hF i j).map.comp
    (ContinuousLinearMap.proj j)

@[expose] def rows : Coordinates e D openV hb hb1 →L[ℂ] Coordinates e D openV hb hb1 :=
  ContinuousLinearMap.pi (row μ e D atlas openV hb hb1 hbu hu1 hw support F hF)

include μ atlas hbu hu1 hw support hF in
omit [CompactSpace M] in
theorem row_physical (i:D.indices) (z:Coordinates e D openV hb hb1) (y:E) :
    EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
      (row μ e D atlas openV hb hb1 hbu hu1 hw support F hF i z) y=
    ChartLocalization.coordinate (e i) (D.cutoff i)
      (fun x=>w x*ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z (F x)) y := by
  classical
  calc
    _ = ∑j:D.indices,EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
      ((transport μ e D atlas openV hb hb1 hbu hu1 hw support F hF i j).map (z j)) y := by
      simp only [row,sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
        map_sum,BoundedContinuousFunction.sum_apply]
    _ = ∑j:D.indices,ChartLocalization.coordinate (e i) (D.cutoff i)
      (fun x=>w x*SupportedChartExtension.function (e j)
        (EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure j) hb hb1 (z j)) (F x)) y := by
      apply Finset.sum_congr rfl
      intro j _
      exact (transport μ e D atlas openV hb hb1 hbu hu1 hw support F hF i j).physical (z j) y
    _ = _ := by
      by_cases hy:y∈(e i).target
      · simp only [ChartLocalization.coordinate,ite_eq_left hy]
        rw [ManifoldHolderLocalizationOperators.reconstruction_apply]
        simp only [Finset.mul_sum]
      · simp only [ChartLocalization.coordinate,ite_eq_right hy,Finset.sum_const_zero]

include μ atlas region hbu hu1 hw support hF in
omit [CompactSpace M] in
theorem reconstruction_rows (z:Coordinates e D openV hb hb1) (x:M) :
    ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1
      (rows μ e D atlas openV hb hb1 hbu hu1 hw support F hF z) x=
    w x*ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z (F x) := by
  let f:M→ℂ := fun x=>w x*ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z (F x)
  have supported:tsupport f⊆S := tsupport_mul_subset_left.trans (support.trans region)
  calc
    _ = ∑i:D.indices,SupportedChartExtension.function (e i)
      (EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
        (rows μ e D atlas openV hb hb1 hbu hu1 hw support F hF z i)) x :=
      ManifoldHolderLocalizationOperators.reconstruction_apply e D openV hb hb1 _ x
    _ = ∑i:D.indices,SupportedChartExtension.function (e i)
      (ChartLocalization.coordinate (e i) (D.cutoff i) f) x := by
      apply Finset.sum_congr rfl
      intro i _
      unfold SupportedChartExtension.function
      by_cases hx:x∈(e i).source
      · rw [ite_eq_left hx,ite_eq_left hx]
        exact row_physical μ e D atlas openV hb hb1 hbu hu1 hw support F hF i z (e i x)
      · rw [ite_eq_right hx,ite_eq_right hx]
    _ = _ := ChartPartitionReconstruction.reconstruct e D f supported x

@[expose] def onCoordinates : Coordinates e D openV hb hb1 →L[ℂ] Regular e D openV hb hb1 :=
  (ManifoldHolderQuotient.quotient (regions e D openV) hb hb1).comp
    (rows μ e D atlas openV hb hb1 hbu hu1 hw support F hF)

include μ atlas region hbu hu1 hw support hF in
omit [CompactSpace M] in
theorem onCoordinates_kernel :
    (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1).ker ≤
      (onCoordinates μ e D atlas openV hb hb1 hbu hu1 hw support F hF).ker := by
  intro z hz
  change onCoordinates μ e D atlas openV hb hb1 hbu hu1 hw support F hF z=0
  apply ManifoldHolderQuotient.physical_injective
  ext x
  have eqn := reconstruction_rows μ e D atlas openV region hb hb1 hbu hu1 hw support F hF z x
  have zero:ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z=0 := hz
  exact (congrArg (fun f:M→ᵇℂ=>f x) (ManifoldHolderQuotient.physical_quotient
    (regions e D openV) hb hb1 (rows μ e D atlas openV hb hb1 hbu hu1 hw support F hF z))).trans
      (eqn.trans (by rw [zero];simp only [map_zero,BoundedContinuousFunction.coe_zero,Pi.zero_apply,mul_zero]))

@[expose] def operator : Regular e D openV hb hb1 →L[ℂ] Regular e D openV hb hb1 :=
  (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1).ker.liftQL
    (onCoordinates μ e D atlas openV hb hb1 hbu hu1 hw support F hF)
    (onCoordinates_kernel μ e D atlas openV region hb hb1 hbu hu1 hw support F hF)

include μ atlas region hbu hu1 hw support hF in
omit [CompactSpace M] in
theorem physical_operator (v:Regular e D openV hb hb1) (x:M) :
    ManifoldSmoothHolderCore.physical e D openV hb hb1
      (operator μ e D atlas openV region hb hb1 hbu hu1 hw support F hF v) x=
    w x*ManifoldSmoothHolderCore.physical e D openV hb hb1 v (F x) := by
  refine Submodule.Quotient.induction_on
    (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1).ker v ?_
  intro z
  exact (congrArg (fun f:M→ᵇℂ=>f x) (ManifoldHolderQuotient.physical_quotient
    (regions e D openV) hb hb1 (rows μ e D atlas openV hb hb1 hbu hu1 hw support F hF z))).trans
      ((reconstruction_rows μ e D atlas openV region hb hb1 hbu hu1 hw support F hF z x).trans
        (congrArg (fun f:M→ᵇℂ=>w x*f (F x))
          (ManifoldHolderQuotient.physical_quotient (regions e D openV) hb hb1 z)).symm)
end LeanShared.ManifoldWeightedHolderOperator
