module
public import LeanShared.Geometry.ManifoldHolderQuotient
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Geometry.ChartLocalizedSupport
public import LeanShared.Geometry.SmoothSupportedManifoldCore

/-! Actual smooth manifold core in the constructed quotient lower space. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
namespace LeanShared.ManifoldSmoothHolderCore
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)

@[expose] def regions : ChartSmoothingRegions.Data
    (fun i : D.indices => e i) (ConstructedManifoldLocalization.support e D) V :=
  ChartSmoothingRegions.data _ _ (ConstructedManifoldLocalization.support_compact e D)
    (fun i => ChartLocalization.localSupport_subset_target (e i) (D.cutoff i) (D.support i)) openV

abbrev Lower := ManifoldHolderQuotient.Space (regions e D openV) hb hb1

local instance lowerNormed : NormedAddCommGroup (Lower e D openV hb hb1) := inferInstance
local instance lowerSeminormed : SeminormedAddCommGroup (Lower e D openV hb hb1) :=
  (lowerNormed e D openV hb hb1).toSeminormedAddCommGroup
local instance lowerScalar : NormedSpace ℂ (Lower e D openV hb hb1) := inferInstance

@[expose] def localCore (i : D.indices) : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    SmoothSupportedManifoldCore.core (E := E) ((regions e D openV).region i) where
  toFun c :=
    ⟨ChartLocalization.coordinate (e i) (D.cutoff i) c.val,
      (ChartLocalization.coordinate_contDiff (e i) (D.cutoff i) (D.support i)
        (atlas i) (D.smooth i) (D.compact i) c.val c.property.1).contMDiff,
      by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := ChartLocalizedSupport.subset (e i) (D.cutoff i) c.val
          (D.support i) (D.compact i) hy
        apply (regions e D openV).contains i
        exact ⟨⟨x, hx.1, rfl⟩, by
          change (e i).symm (e i x) ∈ V
          rw [(e i).left_inv (D.support i hx.1)]
          exact c.property.2 hx.2⟩⟩
  map_add' c f := by
    apply Subtype.ext
    funext y
    change ChartLocalization.coordinate (e i) (D.cutoff i) (c+f).val y =
      ChartLocalization.coordinate (e i) (D.cutoff i) c.val y + ChartLocalization.coordinate (e i) (D.cutoff i) f.val y
    by_cases hy : y ∈ (e i).target
    · simp only [ChartLocalization.coordinate, ite_eq_left hy, Submodule.coe_add, Pi.add_apply, mul_add]
    · simp only [ChartLocalization.coordinate, ite_eq_right hy, add_zero]
  map_smul' z c := by
    apply Subtype.ext
    funext y
    change ChartLocalization.coordinate (e i) (D.cutoff i) (z • c).val y =
      z • ChartLocalization.coordinate (e i) (D.cutoff i) c.val y
    by_cases hy : y ∈ (e i).target
    · simp only [ChartLocalization.coordinate, ite_eq_left hy, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [ChartLocalization.coordinate, ite_eq_right hy, smul_zero]

@[expose] def smoothCoordinates : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    ManifoldHolderQuotient.Coordinates (regions e D openV) hb hb1 :=
  LinearMap.pi fun i =>
    (EuclideanSmoothHolderCore.smooth ((regions e D openV).compact_closure i) hb hb1).comp
      (localCore e D atlas openV i)

@[expose] def smooth : SmoothSupportedManifoldCore.core (E := E) V →ₗ[ℂ]
    Lower e D openV hb hb1 :=
  (ManifoldHolderQuotient.quotient (regions e D openV) hb hb1).toLinearMap.comp
    (smoothCoordinates e D atlas openV hb hb1)

@[expose] def physical : Lower e D openV hb hb1 →L[ℂ] (M →ᵇ ℂ) :=
  ManifoldHolderQuotient.physical (regions e D openV) hb hb1

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem physical_smooth (region : V ⊆ S) (c : SmoothSupportedManifoldCore.core (E := E) V) (x : M) :
    physical e D openV hb hb1 (smooth e D atlas openV hb hb1 c) x = c.val x := by
  classical
  have reconstruct : (∑ i : D.indices, if x ∈ (e i).source then
      ChartLocalization.coordinate (e i) (D.cutoff i) c.val (e i x) else 0) = c.val x := by
    have branch (i : D.indices) : (if x ∈ (e i).source then
        ChartLocalization.coordinate (e i) (D.cutoff i) c.val (e i x) else 0) = D.cutoff i x * c.val x := by
      by_cases hx : x ∈ (e i).source
      · rw [ite_eq_left hx]
        exact ChartLocalization.coordinate_chart (e i) (D.cutoff i) c.val x hx
      · rw [ite_eq_right hx]
        have zero : D.cutoff i x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (D.support i hs))
        rw [zero, zero_mul]
    simp_rw [branch]
    rw [← Finset.sum_mul]
    by_cases hx : x ∈ S
    · rw [D.partition x hx, one_mul]
    · have zero : c.val x = 0 := SmoothSupportedManifoldCore.zero_outside V c x (fun hv => hx (region hv))
      rw [zero, mul_zero]
  let r := regions e D openV
  let z := smoothCoordinates e D atlas openV hb hb1 c
  have raw := congrArg (fun f : M →ᵇ ℂ => f x)
    (ManifoldHolderQuotient.physical_quotient r hb hb1 z)
  have formula := FiniteHolderChartPatching.reconstruction_apply b
    (fun i : D.indices => closure (r.region i)) r.compact_closure
    (fun i : D.indices => e i) r.closure_target
    (ManifoldHolderQuotient.supportedCoordinates r hb hb1 z) x
  calc
    _ = ManifoldHolderQuotient.reconstruction r hb hb1 z x := raw
    _ = ∑ i : D.indices, SupportedHolderChartSpace.realization (r.compact_closure i)
          (e i) (r.closure_target i) (ManifoldHolderQuotient.supportedCoordinates r hb hb1 z i) x := formula
    _ = ∑ i : D.indices, if x ∈ (e i).source then
          ChartLocalization.coordinate (e i) (D.cutoff i) c.val (e i x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = c.val x := reconstruct

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem physical_injective : Function.Injective (physical e D openV hb hb1) :=
  ManifoldHolderQuotient.physical_injective (regions e D openV) hb hb1

include atlas in
omit [CompactSpace M] in
theorem regular (v : Lower e D openV hb hb1) :
    FractionalManifoldRegularity.Regular (E := E) (F := ℂ) b
      (fun x => physical e D openV hb hb1 v x) :=
  ManifoldHolderQuotient.regular (regions e D openV) hb hb1 (fun i => atlas i) v

@[expose] def extendCore (i : D.indices) :
    SmoothSupportedManifoldCore.core (E := E) ((regions e D openV).region i) →ₗ[ℂ]
      SmoothSupportedManifoldCore.core (E := E) V where
  toFun c :=
    ⟨SupportedChartExtension.function (e i) c.val,
      SupportedChartExtension.smooth (e i) (atlas i) c.property.1.contDiff
        (EuclideanSmoothHolderCore.compact_support ((regions e D openV).compact_closure i) c)
        (c.property.2.trans (subset_closure.trans ((regions e D openV).closure_target i))),
      (SupportedChartExtension.support_subset (e i)
        (EuclideanSmoothHolderCore.compact_support ((regions e D openV).compact_closure i) c)
        (c.property.2.trans (subset_closure.trans ((regions e D openV).closure_target i)))).trans (by
          rintro _ ⟨y, hy, rfl⟩
          exact (regions e D openV).inverse_region i y (c.property.2 hy))⟩
  map_add' f g := by
    classical
    apply Subtype.ext
    funext x
    change (if x ∈ (e i).source then (f.val + g.val) (e i x) else 0) =
      (if x ∈ (e i).source then f.val (e i x) else 0) +
      (if x ∈ (e i).source then g.val (e i x) else 0)
    split_ifs <;> simp only [Pi.add_apply, zero_add]
  map_smul' z f := by
    classical
    apply Subtype.ext
    funext x
    change (if x ∈ (e i).source then (z • f.val) (e i x) else 0) =
      z • (if x ∈ (e i).source then f.val (e i x) else 0)
    split_ifs <;> simp only [Pi.smul_apply, smul_zero]

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem quotient_local_smooth (region : V ⊆ S)
    (c : ∀ i : D.indices, SmoothSupportedManifoldCore.core (E := E) ((regions e D openV).region i)) :
    ManifoldHolderQuotient.quotient (regions e D openV) hb hb1
      (fun i => EuclideanSmoothHolderCore.smooth ((regions e D openV).compact_closure i) hb hb1 (c i)) =
      smooth e D atlas openV hb hb1 (∑ i, extendCore e D atlas openV i (c i)) := by
  apply physical_injective e D openV hb hb1
  ext x
  let r := regions e D openV
  let z := fun i => EuclideanSmoothHolderCore.smooth (r.compact_closure i) hb hb1 (c i)
  have raw := congrArg (fun f : M →ᵇ ℂ => f x)
    (ManifoldHolderQuotient.physical_quotient r hb hb1 z)
  have formula := FiniteHolderChartPatching.reconstruction_apply b
    (fun i : D.indices => closure (r.region i)) r.compact_closure
    (fun i : D.indices => e i) r.closure_target
    (ManifoldHolderQuotient.supportedCoordinates r hb hb1 z) x
  calc
    _ = ManifoldHolderQuotient.reconstruction r hb hb1 z x := raw
    _ = ∑ i : D.indices, SupportedHolderChartSpace.realization (r.compact_closure i)
          (e i) (r.closure_target i) (ManifoldHolderQuotient.supportedCoordinates r hb hb1 z i) x := formula
    _ = ∑ i : D.indices, (extendCore e D atlas openV i (c i)).val x := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = (∑ i : D.indices, extendCore e D atlas openV i (c i)).val x := by
      simp only [Submodule.coe_sum, Finset.sum_apply]
    _ = _ := (physical_smooth e D atlas openV hb hb1 region _ x).symm

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem smooth_dense (region : V ⊆ S) :
    DenseRange (fun c : SmoothSupportedManifoldCore.core (E := E) V =>
      (smooth e D atlas openV hb hb1 c : Lower e D openV hb hb1)) := by
  let r := regions e D openV
  have coordinateDense := DenseRange.piMap (fun i : D.indices =>
    EuclideanSmoothHolderCore.smooth_dense (r.compact_closure i) hb hb1)
  have quotientDense :=
    (BanachFunctionQuotient.quotient_surjective (𝕜 := ℂ)
      (H := ManifoldHolderQuotient.Coordinates r hb hb1) (X := M) (F := ℂ)
      (ManifoldHolderQuotient.reconstruction r hb hb1)).denseRange
  have composed := quotientDense.comp coordinateDense (ManifoldHolderQuotient.quotient r hb hb1).continuous
  change Dense (range (smooth e D atlas openV hb hb1))
  apply composed.mono
  rintro _ ⟨c, rfl⟩
  exact ⟨∑ i, extendCore e D atlas openV i (c i), (quotient_local_smooth e D atlas openV hb hb1 region c).symm⟩
end LeanShared.ManifoldSmoothHolderCore
