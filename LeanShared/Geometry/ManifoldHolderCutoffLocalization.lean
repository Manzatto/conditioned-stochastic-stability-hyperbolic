module
public import LeanShared.Geometry.ManifoldHolderLocalizationOperators
public import LeanShared.Geometry.ChartHolderTransport
public import LeanShared.Geometry.EuclideanLittleChartExtension

/-! Localization of the actual finite-chart Holder quotient into ANY genuine
smooth chart. The literal physical formula and the bounded linear map are
constructed from chart transports and quotient descent. -/
public noncomputable section
set_option maxHeartbeats 1600000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction BigOperators
namespace LeanShared.ManifoldHolderCutoffLocalization
variable {E M J:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] {S:Set M}
  (e:J→OpenPartialHomeomorph M E) (D:ConstructedManifoldLocalization.Data e S)
  (atlas:∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V:Set M} (openV:IsOpen V) {b:ℝ} (hb:0<b) (hb1:b<1)
  (c:OpenPartialHomeomorph M E) (hc:c∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  (θ:M→ℂ) (smoothθ:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,ℂ)) ∞ θ)
  (compactθ:HasCompactSupport θ) (supportθ:tsupport θ⊆c.source)

abbrev Coordinates:=ManifoldHolderQuotient.Coordinates (ManifoldSmoothHolderCore.regions e D openV) hb hb1
abbrev Global:=ManifoldSmoothHolderCore.Lower e D openV hb hb1
local instance cutoffCoordinatesNormed : NormedAddCommGroup (Coordinates e D openV hb hb1):=inferInstance
local instance cutoffCoordinatesSemi : SeminormedAddCommGroup (Coordinates e D openV hb hb1):=
  (cutoffCoordinatesNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance cutoffCoordinatesScalar : NormedSpace ℂ (Coordinates e D openV hb hb1):=inferInstance
local instance cutoffGlobalNormed : NormedAddCommGroup (Global e D openV hb hb1):=inferInstance
local instance cutoffGlobalSemi : SeminormedAddCommGroup (Global e D openV hb hb1):=
  (cutoffGlobalNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance cutoffGlobalScalar : NormedSpace ℂ (Global e D openV hb hb1):=inferInstance

 def transport (j:D.indices) : BoundedHolderSpace.graph E b→L[ℂ]BoundedHolderSpace.graph E b:=
  Classical.choose (ChartHolderTransport.exists_transport c (e j) hc (atlas j) θ smoothθ compactθ supportθ
    ((ManifoldSmoothHolderCore.regions e D openV).compact_closure j)
    ((ManifoldSmoothHolderCore.regions e D openV).closure_target j) hb.le hb1.le)

 def row : Coordinates e D openV hb hb1→L[ℂ]BoundedHolderSpace.graph E b:=
  ∑j:D.indices,((transport e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ j).comp
    (EuclideanSmoothHolderCore.space ((ManifoldSmoothHolderCore.regions e D openV).compact_closure j) hb hb1).subtypeL).comp
      (ContinuousLinearMap.proj j)

 theorem row_physical (z:Coordinates e D openV hb hb1) (y:E) :
    BoundedHolderSpace.physical E b (row e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z) y=
      ChartLocalization.coordinate c θ
        (ManifoldHolderQuotient.reconstruction (ManifoldSmoothHolderCore.regions e D openV) hb hb1 z) y :=by
  classical
  calc
    _ = ∑j:D.indices,BoundedHolderSpace.physical E b
        (transport e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ j (z j).val) y:=by
      simp only [row,sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,map_sum,
        BoundedContinuousFunction.sum_apply,Submodule.subtypeL_apply]
    _ = ∑j:D.indices,ChartLocalization.coordinate c θ
        (SupportedChartExtension.function (e j)
          (EuclideanSmoothHolderCore.physical ((ManifoldSmoothHolderCore.regions e D openV).compact_closure j)
            hb hb1 (z j))) y:=by
      apply Finset.sum_congr rfl
      intro j _
      exact Classical.choose_spec (ChartHolderTransport.exists_transport c (e j) hc (atlas j)
        θ smoothθ compactθ supportθ ((ManifoldSmoothHolderCore.regions e D openV).compact_closure j)
        ((ManifoldSmoothHolderCore.regions e D openV).closure_target j) hb.le hb1.le) (z j).val
        (fun q hq=>EuclideanLittleChartExtension.zero_outside_closure
          ((ManifoldSmoothHolderCore.regions e D openV).compact_closure j) hb hb1 (z j) q hq) y
    _ = _:=by
      by_cases hy:y∈c.target
      · simp only [ChartLocalization.coordinate,ite_eq_left hy]
        rw [ManifoldHolderLocalizationOperators.reconstruction_apply,Finset.mul_sum]
      · simp only [ChartLocalization.coordinate,ite_eq_right hy,Finset.sum_const_zero]

 theorem row_kernel :
    (ManifoldHolderQuotient.reconstruction (ManifoldSmoothHolderCore.regions e D openV) hb hb1).ker≤
      (row e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ).ker:=by
  intro z hz
  change row e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z=0
  apply BoundedHolderSpace.physical_injective E b
  ext y
  have formula:=row_physical e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z y
  have zero:ManifoldHolderQuotient.reconstruction (ManifoldSmoothHolderCore.regions e D openV) hb hb1 z=0:=hz
  rw [zero] at formula
  simpa only [ChartLocalization.coordinate,BoundedContinuousFunction.coe_zero,Pi.zero_apply,mul_zero,ite_self,map_zero]
    using formula

 def localization : Global e D openV hb hb1→L[ℂ]BoundedHolderSpace.graph E b:=
  (ManifoldHolderQuotient.reconstruction (ManifoldSmoothHolderCore.regions e D openV) hb hb1).ker.liftQL
    (row e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ)
    (row_kernel e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ)

 theorem physical_localization (v:Global e D openV hb hb1) (y:E) :
    BoundedHolderSpace.physical E b (localization e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ v) y=
      ChartLocalization.coordinate c θ (ManifoldSmoothHolderCore.physical e D openV hb hb1 v) y :=by
  obtain ⟨z,rfl⟩:=BanachFunctionQuotient.quotient_surjective (𝕜:=ℂ)
    (H:=Coordinates e D openV hb hb1) (X:=M) (F:=ℂ)
    (ManifoldHolderQuotient.reconstruction (ManifoldSmoothHolderCore.regions e D openV) hb hb1) v
  change BoundedHolderSpace.physical E b (row e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z) y=
    ChartLocalization.coordinate c θ
      (ManifoldHolderQuotient.physical (ManifoldSmoothHolderCore.regions e D openV) hb hb1
        (ManifoldHolderQuotient.quotient (ManifoldSmoothHolderCore.regions e D openV) hb hb1 z)) y
  rw [ManifoldHolderQuotient.physical_quotient]
  exact row_physical e D atlas openV hb hb1 c hc θ smoothθ compactθ supportθ z y
end LeanShared.ManifoldHolderCutoffLocalization
