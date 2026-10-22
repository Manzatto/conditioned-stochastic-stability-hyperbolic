module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseNativeInterpolation
public import ConditionedStochasticStabilityHyperbolic.Paper.ComputedAnalyticInverseInputs
public import LeanShared.Geometry.NativeFullHolderTests

/-! The remaining actual full-test action source is constructed from original
regular noise and a genuinely fractional departure weight. All inverse
membership, operator bounds and power interpolation are proved. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle MeasureTheory Measure
open LeanShared
open scoped Topology Manifold ContDiff Bundle NNReal BoundedContinuousFunction

set_option maxHeartbeats 6400000 in
theorem InverseFamily.native_testActionInputs
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
    (regularW : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q w) :
    Nonempty (RegularLayerClassicalInputs.TestActionInputs J s w
      (NativeFullHolderTests.view (E := E) (M := M) b (hba.trans ha1).le)
      (NativeFullHolderTests.view_injective (E := E) (M := M) b (hba.trans ha1).le)
      (NativeFullHolderTests.core (E := E) (M := M) b (hba.trans ha1).le)) := by
  classical
  let Test := NativeFullHolderTests.Full (E := E) (M := M) b (hba.trans ha1).le
  let view := NativeFullHolderTests.view (E := E) (M := M) b (hba.trans ha1).le
  let inj := NativeFullHolderTests.view_injective (E := E) (M := M) b (hba.trans ha1).le
  let qt := NativeFullHolderTests.core (E := E) (M := M) b (hba.trans ha1).le
  obtain ⟨ηa,haη,wa,K,hK,actions⟩ := J.jacobianWeight_native_action s μ hb hba ha ha1 lower
    regular inverse w q lowerW regularW 1 zero_lt_one
  obtain ⟨ηi,hiη,wi,interpolations⟩ := J.jacobianWeight_native_interpolation s μ hb hba ha ha1 lower
    regular inverse w q lowerW regularW 1 zero_lt_one
  let η := min ηa ηi
  have hη : 0 < η := lt_min haη hiη
  have window : η ≤ J.window := (min_le_left _ _).trans wa
  have candidates (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ η) (z : FixedControl (ι := ι)) :
      ∃ A : Test →L[ℂ] Test,
        (∀ f x, view (A f) x = (J.fixedJacobianWeight s w ε (x,z) : ℂ)*
          view f (J.fixedInverseMap ε z x)) ∧ ‖A‖ ≤ K := by
    let control := (NoiseCubeRescaling.rescale (ε : ℝ) hp) z
    obtain ⟨A,formula,normA⟩ := actions ε hp (hw.trans (min_le_left _ _)) control
    refine ⟨A,?_,normA⟩
    intro f x
    have actual := formula f x
    change view (A f) x = (J.jacobianWeight s w 1 ε (x,control) : ℂ)*view f (J.map ε (control.val,x)) at actual
    simpa only [InverseFamily.fixedJacobianWeight,InverseFamily.fixedInverseMap,dite_eq_left hp,control] using actual
  let A (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ η) (z : FixedControl (ι := ι)) :=
    Classical.choose (candidates ε hp hw z)
  have formula ε hp hw z f x := (Classical.choose_spec (candidates ε hp hw z)).1 f x
  have normA ε hp hw z := (Classical.choose_spec (candidates ε hp hw z)).2
  let ordinary (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ η) :
      InverseRegularTransfer.OrdinarySources view (J.fixedInverseMap ε) (J.fixedJacobianWeight s w ε) := {
    membership := fun z f => ⟨A ε hp hw z f,funext (formula ε hp hw z f)⟩
    bound := K
    bound_nonnegative := hK
    norm_bound := by
      intro z f v identity
      have same : v = A ε hp hw z f := inj (identity.trans (funext (formula ε hp hw z f)).symm)
      rw [same]
      exact ((A ε hp hw z).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (normA ε hp hw z) (norm_nonneg f)) }
  have interpolation (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ η)
      (c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M)) :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ z₀ z e, 0 ≤ e →
        (∀ x, ‖view ((ordinary ε hp hw).operator inj z (qt c)) x-
          view ((ordinary ε hp hw).operator inj z₀ (qt c)) x‖ ≤ e) →
        dist ((ordinary ε hp hw).operator inj z (qt c))
          ((ordinary ε hp hw).operator inj z₀ (qt c)) ≤ D*e^((a-b)/a) := by
    let rescale := NoiseCubeRescaling.rescale (ι := ι) (ε : ℝ) hp
    let operators := fun z : cube (ι := ι) ε => (ordinary ε hp hw).operator inj (rescale.symm z)
    have actual z f x := (ordinary ε hp hw).operator_function inj (rescale.symm z) f x
    have action z f x : view (operators z f) x = (J.jacobianWeight s w 1 ε (x,z) : ℂ)*
        view f (J.map ε (z.val,x)) := by
      simpa only [InverseFamily.fixedJacobianWeight,InverseFamily.fixedInverseMap,dite_eq_left hp,
        rescale,Homeomorph.apply_symm_apply,view] using actual z f x
    obtain ⟨D,hD,bound⟩ := interpolations ε hp (hw.trans (min_le_right _ _)) operators action c
    refine ⟨D,hD,fun z₀ z e he error => ?_⟩
    have estimate := bound (rescale z₀) (rescale z) e he (by
      simpa only [operators,Homeomorph.symm_apply_apply,view,qt,NativeFullHolderTests.view,NativeFullHolderTests.core,SmoothHolderTestSpaces.view,LinearMap.coe_mk,AddHom.coe_mk] using error)
    simpa only [operators,Homeomorph.symm_apply_apply,qt,NativeFullHolderTests.core] using estimate
  let constant := fun ε c (_z : FixedControl (ι := ι)) =>
    if h : 0 < ε ∧ ε ≤ η then Classical.choose (interpolation ε h.1 h.2 c) else 0
  refine ⟨{
    window := η
    positive := hη
    window_le := window
    regular := ordinary
    smooth_continuous := fun c => by
      change Continuous (fun x => c.val x)
      exact c.property.1.continuous
    exponent := (a-b)/a
    exponent_positive := div_pos (sub_pos.mpr hba) ha
    constant := constant
    interpolation := ?_ }⟩
  intro ε hp hw c z₀ z e he error
  have estimate := (Classical.choose_spec (interpolation ε hp hw c)).2 z₀ z e he error
  simpa only [constant,dite_eq_left (show 0 < ε ∧ ε ≤ η from ⟨hp,hw⟩)] using estimate

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
