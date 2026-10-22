module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseFractionalWeightRegularity
public import LeanShared.Geometry.NativeLittleWeightedOperator

/-! The original regular-noise inverse has a uniformly bounded actual
weighted action on the native little Holder completion. Its inverse weight,
fractional regularity, smooth approximation and operator bound are all
constructed, including original weight regularity below C1. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle MeasureTheory Measure
open scoped Topology Manifold ContDiff Bundle NNReal BoundedContinuousFunction

set_option maxHeartbeats 3200000 in
theorem InverseFamily.jacobianWeight_native_action
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
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ control : cube (ι := ι) ε,
      let weight := fun x => (J.jacobianWeight s w R ε (x,control) : ℂ)
      let inverseMap := fun x => J.map ε (control.val,x)
      let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
      ∃ A : LeanShared.SmoothHolderTestSpaces.space b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ →L[ℂ]
        LeanShared.SmoothHolderTestSpaces.space b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ,
        (∀ v x, LeanShared.SmoothHolderTestSpaces.physical b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ (A v) x =
          weight x*LeanShared.SmoothHolderTestSpaces.physical b
          (LeanShared.BoundedRiemannianMetric.smooth_core_holder (E := E) (M := M) b (hba.trans ha1).le) univ v (inverseMap x)) ∧
        ‖A‖ ≤ K := by
  classical
  obtain ⟨ηr,hr,wr,regularWeights⟩ := J.jacobianWeight_fractional_regular s μ ha ha1 lower
    regular inverse w q lowerW regularW R hR
  obtain ⟨ηh,hh,wh,B,C,hB,hC,holderWeights⟩ := J.jacobianWeight_fractional_global_holder s μ hb
    (hba.trans ha1) (by linarith) regular inverse w q (hba.trans lowerW) regularW R hR
  have one : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using (show (1:ℝ) ≤ r by linarith))
  obtain ⟨ηg,hg,wg,L,lipG⟩ := J.uniform_native_lipschitz (by linarith)
    (regular.differentiable.of_le (by exact_mod_cast one)) inverse
  let η := min ηr (min ηh ηg)
  have positive : 0 < η := lt_min hr (lt_min hh hg)
  have window : η ≤ J.window := (min_le_left _ _).trans wr
  refine ⟨η,positive,window,max B (B*(L:ℝ)^b+C),le_trans hB (le_max_left _ _),?_⟩
  intro ε hp hw control
  let weight := fun x => (J.jacobianWeight s w R ε (x,control) : ℂ)
  let inverseMap := fun x => J.map ε (control.val,x)
  have continuous : Continuous weight := Complex.continuous_ofReal.comp
    ((J.jacobianWeight_continuous s μ w regularW.differentiable.continuous R ε hp (hw.trans window)).comp
      (continuous_id.prodMk (continuous_const (y := control))))
  let ψ : M →ᵇ ℂ := BoundedContinuousFunction.mkOfCompact ⟨weight,continuous⟩
  have regularψ : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := ℂ) a ψ :=
    regularWeights ε hp (hw.trans (min_le_left _ _)) control
  have values := holderWeights ε hp (hw.trans ((min_le_right _ _).trans (min_le_left _ _))) control
  have normψ : ‖ψ‖ ≤ B := (BoundedContinuousFunction.norm_le hB).mpr (fun x => by
    change ‖(J.jacobianWeight s w R ε (x,control) : ℂ)‖ ≤ B
    simpa only [Complex.norm_real,Real.norm_eq_abs] using values.1 x)
  have lip := lipG ε hp (hw.trans ((min_le_right _ _).trans (min_le_right _ _))) (hw.trans window) control
  have smoothInverse := J.map_contMDiff ε hp (hw.trans window) control
  let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
  have holder : ∀ x y, ‖ψ x-ψ y‖ ≤ C*dist x y^b := by
    intro x y
    change ‖(weight x)-(weight y)‖ ≤ C*dist x y^b
    simpa only [weight,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using values.2 x y
  let e := fun x : M => chartAt E x
  let D := LeanShared.ConstructedManifoldLocalization.data e isCompact_univ
    (fun x _ => mem_iUnion.mpr ⟨x,mem_chart_source E x⟩)
  obtain ⟨A,formula,normA⟩ := LeanShared.SmoothHolderTestSpaces.exists_weighted_operator μ e D
    (fun x => chart_mem_maximalAtlas x) isOpen_univ (Subset.rfl) hb (hba.trans ha1) hba ha1 ψ regularψ
    (subset_univ _) inverseMap smoothInverse hC holder lip
  refine ⟨A,formula,normA.trans ?_⟩
  exact max_le_max normψ (add_le_add
    (mul_le_mul_of_nonneg_right normψ (Real.rpow_nonneg L.coe_nonneg b)) le_rfl)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
