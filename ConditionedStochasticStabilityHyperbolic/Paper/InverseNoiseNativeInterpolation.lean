module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseNativeLittleAction
public import LeanShared.Analysis.WeightedHolderFamilyInterpolation

/-! The interpolation contract for the computed original inverse actions
is proved from uniform higher fractional weight and inverse Lipschitz
bounds. The exact operators can be any of the already constructed native
operators with their literal action; no control continuity is assumed. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle MeasureTheory Measure
open scoped Topology Manifold ContDiff Bundle NNReal BoundedContinuousFunction

set_option maxHeartbeats 3200000 in
theorem InverseFamily.jacobianWeight_native_interpolation
    {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r a b : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (s : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (hb : 0 < b) (hba : b < a) (ha : 0 < a) (ha1 : a < 1) (lower : a+1 < r)
    (regular : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (w : M → ℝ) (q : ℝ) (lowerW : a < q)
    (regularW : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q w)
    (R : ℝ) (hR : 0 < R) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧
      ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η →
      let weight := fun (z : cube (ι := ι) ε) x => (J.jacobianWeight s w R ε (x,z) : ℂ)
      let inverseMap := fun (z : cube (ι := ι) ε) x => J.map ε (z.val,x)
      let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
      ∀ A : cube (ι := ι) ε → (LeanShared.SmoothHolderTestSpaces.space b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ) →L[ℂ] (LeanShared.SmoothHolderTestSpaces.space b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ),
        (∀ z v x, LeanShared.SmoothHolderTestSpaces.physical b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ (A z v) x =
          weight z x*LeanShared.SmoothHolderTestSpaces.physical b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ v (inverseMap z x)) →
        ∀ c : LeanShared.SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ z₀ z e, 0 ≤ e →
          (∀ x, ‖LeanShared.SmoothHolderTestSpaces.physical b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ (A z (LeanShared.SmoothHolderTestSpaces.coreMap b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ c)) x-
            LeanShared.SmoothHolderTestSpaces.physical b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ (A z₀ (LeanShared.SmoothHolderTestSpaces.coreMap b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ c)) x‖ ≤ e) →
          dist (A z (LeanShared.SmoothHolderTestSpaces.coreMap b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ c)) (A z₀ (LeanShared.SmoothHolderTestSpaces.coreMap b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ c)) ≤ K*e^((a-b)/a) := by
  classical
  obtain ⟨ηh,hh,wh,B,C,hB,hC,holderWeights⟩ := J.jacobianWeight_fractional_global_holder s μ ha
    ha1 lower regular inverse w q lowerW regularW R hR
  have one : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using (show (1:ℝ) ≤ r by linarith))
  obtain ⟨ηg,hg,wg,L,lipG⟩ := J.uniform_native_lipschitz (by linarith)
    (regular.differentiable.of_le (by exact_mod_cast one)) inverse
  let η := min ηh ηg
  have positive : 0 < η := lt_min hh hg
  have window : η ≤ J.window := (min_le_left _ _).trans wh
  refine ⟨η,positive,window,fun ε hp hw => ?_⟩
  let weight := fun (z : cube (ι := ι) ε) x => (J.jacobianWeight s w R ε (x,z) : ℂ)
  let inverseMap := fun (z : cube (ι := ι) ε) x => J.map ε (z.val,x)
  have continuous (z : cube (ι := ι) ε) : Continuous (weight z) := Complex.continuous_ofReal.comp
    ((J.jacobianWeight_continuous s μ w regularW.differentiable.continuous R ε hp (hw.trans window)).comp
      (continuous_id.prodMk (continuous_const (y := z))))
  let ψ := fun z : cube (ι := ι) ε => BoundedContinuousFunction.mkOfCompact ⟨weight z,continuous z⟩
  have values (z : cube (ι := ι) ε) := holderWeights ε hp (hw.trans (min_le_left _ _)) z
  have normψ (z : cube (ι := ι) ε) : ‖ψ z‖ ≤ B := (BoundedContinuousFunction.norm_le hB).mpr (fun x => by
    change ‖(J.jacobianWeight s w R ε (x,z) : ℂ)‖ ≤ B
    simpa only [Complex.norm_real,Real.norm_eq_abs] using (values z).1 x)
  have lip (z : cube (ι := ι) ε) := lipG ε hp (hw.trans (min_le_right _ _)) (hw.trans window) z
  let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
  let certificate := LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le
  change ∀ A : cube (ι := ι) ε → LeanShared.SmoothHolderTestSpaces.space b certificate univ →L[ℂ]
    LeanShared.SmoothHolderTestSpaces.space b certificate univ, _
  intro A formula c
  let f := LeanShared.SmoothHolderTestSpaces.holderCore a
    (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) a ha1.le) univ c
  let v := fun z => (A z (LeanShared.SmoothHolderTestSpaces.coreMap b certificate univ c)).val
  let K := 2*((B*(L:ℝ)^a+C)*‖f‖)+6*(B*‖f‖)+3
  refine ⟨K,by dsimp only [K]; positivity,fun z₀ z e he error => ?_⟩
  have weights (z : cube (ι := ι) ε) x y : ‖ψ z x-ψ z y‖ ≤ C*dist x y^a := by
    change ‖weight z x-weight z y‖ ≤ _
    simpa only [weight,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using (values z).2 x y
  have physical (z : cube (ι := ι) ε) x : LeanShared.BoundedHolderSpace.physical M b (v z) x =
      ψ z x*LeanShared.BoundedHolderSpace.physical M a f (inverseMap z x) := formula z _ x
  have estimate := LeanShared.HolderWeightComposition.family_interpolation hb.le hba hB hC ψ normψ weights
    inverseMap lip f v physical z z₀ he error
  rw [dist_eq_norm]
  change ‖v z-v z₀‖ ≤ K*e^((a-b)/a)
  exact estimate

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
