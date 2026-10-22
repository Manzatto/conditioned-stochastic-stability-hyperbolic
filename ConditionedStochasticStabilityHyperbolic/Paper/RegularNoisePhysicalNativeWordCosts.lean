module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseUniformNativeWordCost
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseValidItinerary

/-! Native cost convergence and uniform noise windows on actual manifold
points. A genuine finite Whitney itinerary is constructed internally, so no
chart-domain or Jacobian limit source is required from the caller. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff NNReal BigOperators
open LeanShared LeanShared.FiniteJetComposition HyperbolicBasicSet FiniteSmoothCapturePartition
variable {E M ι I A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {v : I → Set M}

theorem Maps.moving_physical_nativeCost_tendsto
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (N : ℕ) (labels : Fin (N+1) → I)
    (ε : A → ℝ≥0) (controls : ℕ → ∀ i, cube (ι := ι) (ε i)) (l : Filter A)
    (limit : Tendsto ε l (𝓝 0)) (positive : ∀ᶠ i in l, 0 < ε i)
    (x₀ : M) (collar : x₀ ∈ a.collar) (x : A → M) (moving : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => nativeWordCost a d g
      (fun n => F.family (ε i) (controls n i).val) N labels (x i)) l
      (𝓝 (nativeWordCost a d g (fun _ => T) N labels x₀)) := by
  have cover (n : ℕ) : ∃ i, (T : M → M)^[n] x₀ ∈ F.atlas.patch i := by
    have member : (T : M → M)^[n] x₀ ∈ ⋃ i, F.atlas.patch i :=
      F.atlas.patch_cover.symm ▸ mem_univ _
    exact mem_iUnion.mp member
  choose chart patches using cover
  let c := F.atlas.source (chart 0)
  have source : x₀ ∈ c.source := F.atlas.patch_source (chart 0) (subset_closure (patches 0))
  have inside := F.atlas.mem_actualWordDomain_of_patch_itinerary chart x₀ patches N
  have back : (F.atlas.source (chart 0)).symm (c x₀) = x₀ := c.left_inv source
  have near : ∀ᶠ i in l, x i ∈ c.source := moving.eventually (c.open_source.mem_nhds source)
  have coordinates := (c.continuousAt source).tendsto.comp moving
  have result := F.moving_word_nativeCost_tendsto regularity deterministic inverse a d g weight
    N labels ε controls l limit positive chart (c x₀) inside
    (by simpa only [back] using collar) (fun i => c (x i)) coordinates
  have corrected := result.congr' (show
      (fun i => nativeWordCost a d g (fun n => F.family (ε i) (controls n i).val) N labels
        (c.symm (c (x i)))) =ᶠ[l]
      (fun i => nativeWordCost a d g (fun n => F.family (ε i) (controls n i).val) N labels
        (x i)) from by
    filter_upwards [near] with i hi
    rw [c.left_inv hi])
  simpa only [back] using corrected

theorem Maps.uniform_physical_nativeCost
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (N : ℕ) (labels : Fin (N+1) → I)
    (K : Set M) (compact : IsCompact K) (collar : K ⊆ a.collar)
    (δ : ℝ) (positive : 0 < δ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ x ∈ K,
        |nativeWordCost a d g (fun n => F.family ε (controls n).val) N labels x -
          nativeWordCost a d g (fun _ => T) N labels x| ≤ δ := by
  obtain ⟨η,hη,bound⟩ := MovingLimitUniformOnCompact.uniform
    (fun ε => ℕ → cube (ι := ι) ε)
    (fun ε controls => nativeWordCost a d g (fun n => F.family ε (controls n).val) N labels)
    (nativeWordCost a d g (fun _ => T) N labels) a.collar K compact collar
    (nativeWordCost_deterministic_continuousOn deterministic inverse a d g weight N labels) (by
      intro ε controls limit pos p hp x moving
      exact F.moving_physical_nativeCost_tendsto regularity deterministic inverse a d g weight
        N labels ε (fun n i => controls i n) atTop limit (Eventually.of_forall pos) p hp x moving)
    δ positive
  exact ⟨η,hη,fun ε hp hs controls x hx => by
    simpa only [Real.norm_eq_abs] using bound ε hp hs controls x hx⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
