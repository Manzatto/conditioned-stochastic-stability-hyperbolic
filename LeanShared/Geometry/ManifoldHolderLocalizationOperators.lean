module
public import LeanShared.Geometry.ManifoldHolderCoordinateOperators

/-! Actual bounded localization of the constructed global lower space into
its chartwise little-Hölder spaces. Reconstruction kernels are annihilated
by the literal function identity, so all maps descend to the quotient. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction BigOperators
namespace LeanShared.ManifoldHolderLocalizationOperators
open ManifoldHolderCoordinateOperators
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0<b) (hb1 : b<1)

abbrev Coordinates := ManifoldHolderQuotient.Coordinates (regions e D openV) hb hb1
local instance coordinatesNormed : NormedAddCommGroup (Coordinates e D openV hb hb1) := inferInstance
local instance coordinatesSemi : SeminormedAddCommGroup (Coordinates e D openV hb hb1) :=
  (coordinatesNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance coordinatesScalar : NormedSpace ℂ (Coordinates e D openV hb hb1) := inferInstance

local instance localNormed (i : D.indices) : NormedAddCommGroup (Local e D openV hb hb1 i) := inferInstance
local instance localSemi (i : D.indices) : SeminormedAddCommGroup (Local e D openV hb hb1 i) :=
  (localNormed e D openV hb hb1 i).toSeminormedAddCommGroup
local instance localScalar (i : D.indices) : NormedSpace ℂ (Local e D openV hb hb1 i) := inferInstance

@[expose] def transport (i j : D.indices) : Transport e D atlas openV hb hb1 i j :=
  Classical.choice (ManifoldHolderCoordinateOperators.exists_transport e D atlas openV hb hb1 i j)

@[expose] def row (i : D.indices) : Coordinates e D openV hb hb1 →L[ℂ] Local e D openV hb hb1 i :=
  ∑j : D.indices, (transport e D atlas openV hb hb1 i j).map.comp (ContinuousLinearMap.proj j)

theorem reconstruction_apply (z : Coordinates e D openV hb hb1) (x : M) :
    ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z x =
      ∑j : D.indices, SupportedChartExtension.function (e j)
        (EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure j) hb hb1 (z j)) x := by
  exact FiniteHolderChartPatching.reconstruction_apply b
    (fun j : D.indices => closure ((regions e D openV).region j)) (regions e D openV).compact_closure
    (fun j : D.indices => e j) (regions e D openV).closure_target
    (ManifoldHolderQuotient.supportedCoordinates (regions e D openV) hb hb1 z) x

theorem row_physical (i : D.indices) (z : Coordinates e D openV hb hb1) (y : E) :
    EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
      (row e D atlas openV hb hb1 i z) y =
      ChartLocalization.coordinate (e i) (D.cutoff i)
        (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z) y := by
  classical
  calc
    _ = ∑j : D.indices, EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
        ((transport e D atlas openV hb hb1 i j).map (z j)) y := by
      simp only [row,sum_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply,map_sum,BoundedContinuousFunction.sum_apply]
    _ = ∑j : D.indices, ChartLocalization.coordinate (e i) (D.cutoff i)
        (SupportedChartExtension.function (e j)
          (EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure j) hb hb1 (z j))) y := by
      apply Finset.sum_congr rfl
      intro j _
      exact (transport e D atlas openV hb hb1 i j).physical (z j) y
    _ = _ := by
      by_cases hy : y∈(e i).target
      · simp only [ChartLocalization.coordinate,ite_eq_left hy]
        rw [reconstruction_apply,Finset.mul_sum]
      · simp only [ChartLocalization.coordinate,ite_eq_right hy,Finset.sum_const_zero]

include atlas in
theorem row_kernel (i : D.indices) :
    (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1).ker ≤
      (row e D atlas openV hb hb1 i).ker := by
  intro z zero
  change row e D atlas openV hb hb1 i z=0
  apply EuclideanSmoothHolderCore.physical_injective ((regions e D openV).compact_closure i) hb hb1
  ext y
  have formula := row_physical e D atlas openV hb hb1 i z y
  have vanishes : ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1 z=0 := zero
  rw [vanishes] at formula
  simpa only [ChartLocalization.coordinate,BoundedContinuousFunction.coe_zero,Pi.zero_apply,mul_zero,ite_self,map_zero] using formula

@[expose] def localization (i : D.indices) :
    ManifoldSmoothHolderCore.Lower e D openV hb hb1 →L[ℂ] Local e D openV hb hb1 i :=
  (ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1).ker.liftQL
    (row e D atlas openV hb hb1 i) (row_kernel e D atlas openV hb hb1 i)
theorem localization_quotient (i : D.indices) (z : Coordinates e D openV hb hb1) :
    localization e D atlas openV hb hb1 i
      (ManifoldHolderQuotient.quotient (regions e D openV) hb hb1 z) =
      row e D atlas openV hb hb1 i z := rfl

include atlas in
theorem localization_smooth (region : V⊆S) (i : D.indices)
    (c : SmoothSupportedManifoldCore.core (E:=E) V) :
    localization e D atlas openV hb hb1 i
      (ManifoldSmoothHolderCore.smooth e D atlas openV hb hb1 c) =
      EuclideanSmoothHolderCore.smooth ((regions e D openV).compact_closure i) hb hb1
        (ManifoldSmoothHolderCore.localCore e D atlas openV i c) := by
  change localization e D atlas openV hb hb1 i
    (ManifoldHolderQuotient.quotient (regions e D openV) hb hb1
      (ManifoldSmoothHolderCore.smoothCoordinates e D atlas openV hb hb1 c)) = _
  rw [localization_quotient]
  apply EuclideanSmoothHolderCore.physical_injective ((regions e D openV).compact_closure i) hb hb1
  ext y
  have formula := row_physical e D atlas openV hb hb1 i
    (ManifoldSmoothHolderCore.smoothCoordinates e D atlas openV hb hb1 c) y
  have reconstructed : (fun x => ManifoldHolderQuotient.reconstruction (regions e D openV) hb hb1
      (ManifoldSmoothHolderCore.smoothCoordinates e D atlas openV hb hb1 c) x) = c.val := by
    funext x
    have raw := congrArg (fun f : M →ᵇ ℂ => f x)
      (ManifoldHolderQuotient.physical_quotient (regions e D openV) hb hb1
        (ManifoldSmoothHolderCore.smoothCoordinates e D atlas openV hb hb1 c))
    exact raw.symm.trans (ManifoldSmoothHolderCore.physical_smooth e D atlas openV hb hb1 region c x)
  change _ = ChartLocalization.coordinate (e i) (D.cutoff i) c.val y
  exact formula.trans (congrArg
    (fun f : M → ℂ => ChartLocalization.coordinate (e i) (D.cutoff i) f y) reconstructed)
end LeanShared.ManifoldHolderLocalizationOperators
