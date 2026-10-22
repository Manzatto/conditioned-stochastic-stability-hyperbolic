module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseNativeWordCostLimit
public import LeanShared.Analysis.MovingLimitUniformOnCompact

/-! The actual localized native cost has one small-noise window on every
compact deterministic Whitney itinerary. The window precedes all controls
and all points; fixed-scale joint regularity is not used as scale continuity. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff NNReal BigOperators
open LeanShared LeanShared.FiniteJetComposition HyperbolicBasicSet FiniteSmoothCapturePartition
variable {E M ι I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι] [Fintype I]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
  {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {v : I → Set M}

theorem nativeWordCost_deterministic_continuousOn
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (N : ℕ) (labels : Fin (N+1) → I) :
    ContinuousOn (nativeWordCost a d g (fun _ => T) N labels) a.collar := by
  have forward : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 (T^N : M ≃ₜ M) := by
    rw [DiffeomorphismIterates.coe_pow]
    exact deterministic.iterate N
  have numerator : Continuous (fun x =>
      wordCutoff d (fun j : Fin (N+1) => (T : M → M)^[j.val] x) labels *
        |∏ j ∈ Finset.range N, g ((T : M → M)^[j] x)|) :=
    (wordCutoff_continuous d _ (fun j => T.continuous.iterate j.val) labels).mul
      ((continuous_finsetProd _ (fun j _ => weight.comp (T.continuous.iterate j))).abs)
  have ratio := a.continuousOn_nativeRatio (T^N) forward
    (DiffeomorphismIterates.mdifferentiable_symm_pow T inverse N) _ numerator
  apply ratio.congr
  intro x hx
  rw [nativeWordCost_deterministic_eq]
  have determinantPow := congrArg (fun f : M → M =>
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f x).toLinearMap.domRestrict (a.unstable x)).normDet)
      (DiffeomorphismIterates.coe_pow T N)
  exact congrArg (fun J : ℝ =>
    wordCutoff d (fun j : Fin (N+1) => (T : M → M)^[j.val] x) labels *
      |∏ j ∈ Finset.range N, g ((T : M → M)^[j] x)| / J) determinantPow.symm

theorem Maps.uniform_word_nativeCost
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    {h : HyperbolicData (E := E) T Λ} (a : h.NormedAdaptedProjection)
    (d : Data (E := E) Λ v) (g : M → ℝ) (weight : Continuous g)
    (chart : ℕ → Fin F.atlas.count) (N : ℕ) (labels : Fin (N+1) → I)
    (K : Set E) (compact : IsCompact K) (inside : K ⊆ F.atlas.actualWordDomain chart N)
    (collar : ∀ y ∈ K, (F.atlas.source (chart 0)).symm y ∈ a.collar)
    (δ : ℝ) (positive : 0 < δ) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ η →
      ∀ controls : ℕ → cube (ι := ι) ε, ∀ y ∈ K,
        |nativeWordCost a d g (fun n => F.family ε (controls n).val) N labels
          ((F.atlas.source (chart 0)).symm y) -
        nativeWordCost a d g (fun _ => T) N labels
          ((F.atlas.source (chart 0)).symm y)| ≤ δ := by
  let c := F.atlas.source (chart 0)
  let U := F.atlas.actualWordDomain chart N ∩ {y | c.symm y ∈ a.collar}
  have continuous : ContinuousOn
      (fun y => nativeWordCost a d g (fun _ => T) N labels (c.symm y)) U :=
    (nativeWordCost_deterministic_continuousOn deterministic inverse a d g weight N labels).comp
      (c.continuousOn_symm.mono (fun _ hy => hy.1.2.1)) (fun _ hy => hy.2)
  obtain ⟨η,hη,bound⟩ := MovingLimitUniformOnCompact.uniform
    (fun ε => ℕ → cube (ι := ι) ε)
    (fun ε controls y => nativeWordCost a d g
      (fun n => F.family ε (controls n).val) N labels (c.symm y))
    (fun y => nativeWordCost a d g (fun _ => T) N labels (c.symm y))
    U K compact (fun y hy => ⟨inside hy,collar y hy⟩) continuous (by
      intro ε controls limit pos p hp y moving
      exact F.moving_word_nativeCost_tendsto regularity deterministic inverse a d g weight N labels
        ε (fun n i => controls i n) atTop limit (Eventually.of_forall pos)
        chart p hp.1 hp.2 y moving) δ positive
  exact ⟨η,hη,fun ε hp hs controls y hy => by
    simpa only [Real.norm_eq_abs] using bound ε hp hs controls y hy⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
