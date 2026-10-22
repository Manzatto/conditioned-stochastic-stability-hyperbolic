module
public import LeanShared.Geometry.ManifoldSmoothHolderCore
public import LeanShared.Geometry.ChartAnyOrderHolderRealization
public import LeanShared.Geometry.ChartPartitionReconstruction

/-! Exact supported rough functions in the constructed finite-chart lower space. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory IsManifold
open scoped Manifold ContDiff Topology BoundedContinuousFunction
namespace LeanShared.ManifoldSmoothHolderCore
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M]
  (μ : Measure E) [μ.IsAddHaarMeasure]
  {S : Set M} (e : J → OpenPartialHomeomorph M E)
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀ i, e i ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) (region : V ⊆ S)
  {u b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hbu : b < u)

@[expose] def RoughFunctions (u : ℝ) (V : Set M) :=
  {f : M → ℂ // FractionalManifoldRegularity.Regular (E := E) (F := ℂ) u f ∧ tsupport f ⊆ V}

include openV in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E] in
theorem rough_coordinate_support (f : RoughFunctions (E := E) u V) (i : D.indices) :
    tsupport (ChartLocalization.coordinate (e i) (D.cutoff i) f.val) ⊆
      (regions e D openV).region i := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := ChartLocalizedSupport.subset (e i) (D.cutoff i) f.val
    (D.support i) (D.compact i) hy
  apply (regions e D openV).contains i
  exact ⟨⟨x, hx.1, rfl⟩, by
    change (e i).symm (e i x) ∈ V
    rw [(e i).left_inv (D.support i hx.1)]
    exact f.property.2 hx.2⟩

include μ atlas hbu in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem rough_coordinate_exists (f : RoughFunctions (E := E) u V) (i : D.indices) :
    ∃ v : EuclideanSmoothHolderCore.space ((regions e D openV).compact_closure i) hb hb1,
      EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1 v =
        ChartFractionalLocalization.bounded (e i) (D.cutoff i) (D.support i) (D.compact i)
          (D.smooth i) f.property.1 :=
  ChartAnyOrderHolderRealization.exists_lower μ (e i) (atlas i) (D.cutoff i)
    (D.support i) (D.compact i) (D.smooth i) hb hb1 hbu f.property.1
    ((regions e D openV).compact_closure i) ((regions e D openV).open_region i)
    (rough_coordinate_support e D openV f i)

@[expose] def roughCoordinates (f : RoughFunctions (E := E) u V) :
    ManifoldHolderQuotient.Coordinates (regions e D openV) hb hb1 :=
  fun i => Classical.choose (rough_coordinate_exists μ e D atlas openV hb hb1 hbu f i)

@[expose] def lower (f : RoughFunctions (E := E) u V) : Lower e D openV hb hb1 :=
  ManifoldHolderQuotient.quotient (regions e D openV) hb hb1
    (roughCoordinates μ e D atlas openV hb hb1 hbu f)

include region in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem physical_lower (f : RoughFunctions (E := E) u V) (x : M) :
    physical e D openV hb hb1 (lower μ e D atlas openV hb hb1 hbu f) x = f.val x := by
  classical
  let r := regions e D openV
  let z := roughCoordinates μ e D atlas openV hb hb1 hbu f
  have raw := congrArg (fun g : M →ᵇ ℂ => g x)
    (ManifoldHolderQuotient.physical_quotient r hb hb1 z)
  have formula := FiniteHolderChartPatching.reconstruction_apply b
    (fun i : D.indices => closure (r.region i)) r.compact_closure
    (fun i : D.indices => e i) r.closure_target
    (ManifoldHolderQuotient.supportedCoordinates r hb hb1 z) x
  calc
    _ = ManifoldHolderQuotient.reconstruction r hb hb1 z x := raw
    _ = ∑ i : D.indices, SupportedHolderChartSpace.realization (r.compact_closure i)
        (e i) (r.closure_target i) (ManifoldHolderQuotient.supportedCoordinates r hb hb1 z i) x := formula
    _ = ∑ i : D.indices, SupportedChartExtension.function (e i)
        (ChartLocalization.coordinate (e i) (D.cutoff i) f.val) x := by
      apply Finset.sum_congr rfl
      intro i _
      have coordinate := Classical.choose_spec
        (rough_coordinate_exists μ e D atlas openV hb hb1 hbu f i)
      change (if x ∈ (e i).source then
        EuclideanSmoothHolderCore.physical (r.compact_closure i) hb hb1 (z i) (e i x) else 0) = _
      by_cases hx : x ∈ (e i).source
      · rw [ite_eq_left hx]
        rw [SupportedChartExtension.function, ite_eq_left hx]
        exact congrArg (fun g : E →ᵇ ℂ => g (e i x)) coordinate
      · simp only [SupportedChartExtension.function, ite_eq_right hx]
    _ = f.val x := ChartPartitionReconstruction.reconstruct e D f.val (f.property.2.trans region) x

@[expose] def view : Lower e D openV hb hb1 →ₗ[ℂ] (M → ℂ) where
  toFun v := physical e D openV hb hb1 v
  map_add' a c := by
    funext x
    exact congrArg (fun g : M →ᵇ ℂ => g x) ((physical e D openV hb hb1).map_add a c)
  map_smul' z c := by
    funext x
    exact congrArg (fun g : M →ᵇ ℂ => g x) ((physical e D openV hb hb1).map_smul z c)

omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E] in
theorem view_injective : Function.Injective (view e D openV hb hb1) := by
  intro f g equal
  apply physical_injective e D openV hb hb1
  ext x
  exact congrFun equal x

include region in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem view_lower (f : RoughFunctions (E := E) u V) :
    view e D openV hb hb1 (lower μ e D atlas openV hb hb1 hbu f) = f.val := by
  funext x
  exact physical_lower μ e D atlas openV region hb hb1 hbu f x

include region in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E] in
theorem view_smooth (c : SmoothSupportedManifoldCore.core (E := E) V) :
    view e D openV hb hb1 (smooth e D atlas openV hb hb1 c) = c.val := by
  funext x
  exact physical_smooth e D atlas openV hb hb1 region c x

include region in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] [MeasurableSpace E] [BorelSpace E] in
theorem exists_smooth_sequence (v : Lower e D openV hb hb1) :
    ∃ c : ℕ → SmoothSupportedManifoldCore.core (E := E) V,
      Tendsto (fun n => smooth e D atlas openV hb hb1 (c n)) atTop (𝓝 v) := by
  have dense := smooth_dense e D atlas openV hb hb1 region
  have member : v ∈ closure (range (smooth e D atlas openV hb hb1)) :=
    dense.closure_range ▸ mem_univ v
  obtain ⟨s, hs, limit⟩ := mem_closure_iff_seq_limit.mp member
  choose c hc using hs
  exact ⟨c, by simpa only [hc] using limit⟩

include region in
omit [IsManifold (𝓘(ℝ,E)) ∞ M] [CompactSpace M] in
theorem approximate (f : RoughFunctions (E := E) u V) :
    ∃ c : ℕ → SmoothSupportedManifoldCore.core (E := E) V,
      Tendsto (fun n => smooth e D atlas openV hb hb1 (c n)) atTop
        (𝓝 (lower μ e D atlas openV hb hb1 hbu f)) :=
  exists_smooth_sequence e D atlas openV region hb hb1 _
end LeanShared.ManifoldSmoothHolderCore
