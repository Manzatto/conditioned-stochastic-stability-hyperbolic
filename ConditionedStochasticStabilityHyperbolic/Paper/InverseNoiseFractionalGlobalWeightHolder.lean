module
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseGlobalReferenceJacobianHolder
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseNativeLipschitz
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseJacobianWeights
public import LeanShared.Geometry.BoundedRiemannianFractionalHolder
import all LeanShared.Geometry.FiniteSmoothReferenceJacobianHolder
import Mathlib.Tactic

/-! Actual normalized inverse weights have uniform native Holder bounds.
The original weight is genuinely fractional C^q, including q<1, the inverse and Jacobian controls are
proved from original regular noise, and no completed test action is assumed. -/
public noncomputable section
set_option maxHeartbeats 3200000
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle MeasureTheory Measure
open scoped Topology Manifold ContDiff Bundle NNReal

theorem InverseFamily.jacobianWeight_fractional_global_holder
    {E M ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r a : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (s : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (ha : 0 < a) (ha1 : a < 1) (lower : a+1 < r)
    (regular : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (w : M → ℝ) (q : ℝ) (lowerW : a < q)
    (regularW : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q w)
    (R : ℝ) (hR : 0 < R) :
    ∃ η : ℝ≥0, 0 < η ∧ η ≤ J.window ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (ε : ℝ≥0), 0 < ε → ε ≤ η → ∀ control : cube (ι := ι) ε,
      (∀ x, |J.jacobianWeight s w R ε (x,control)| ≤ B) ∧
      ∀ x y, |J.jacobianWeight s w R ε (x,control)-J.jacobianWeight s w R ε (y,control)| ≤
        C*(let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E); dist x y)^a := by
  classical
  have one : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ r by linarith))
  have regularT : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T := regular.differentiable.of_le (by exact_mod_cast one)
  obtain ⟨ηj,hηj,wj,Bj,Cj,hBj,hCj,jacobian⟩ := J.referenceJacobian_global_holder s μ ha ha1 lower regular inverse
  obtain ⟨ηg,hηg,wg,Lg,lipG⟩ := J.uniform_native_lipschitz (by linarith) regularT inverse
  obtain ⟨Cw,hCw,holderW⟩ := LeanShared.BoundedRiemannianMetric.real_fractional_exists_holder w ha ha1 lowerW regularW
  obtain ⟨B0,values⟩ := isCompact_univ.exists_bound_of_continuousOn regularW.differentiable.continuous.continuousOn
  let Bw := max 0 B0
  have hBw : 0 ≤ Bw := le_max_left _ _
  let P := Σ ε : {ε : ℝ≥0 // 0 < ε ∧ ε ≤ J.window}, cube (ι := ι) ε.val
  let g : P → M → M := fun p x => J.map p.1.val (p.2.val,x)
  let j : P → M → ℝ := fun p x => s.jacobian (J.homeomorph p.1.val p.1.property.1 p.1.property.2 p.2) x
  let v : P → M → ℝ := fun p x => max (w (g p x)) 0
  let ψ : P → M → ℝ := fun p x => J.jacobianWeight s w R p.1.val (x,p.2)
  have formula (p : P) (x : M) : ψ p x = (v p x*j p x)/R := by
    dsimp only [ψ,v,g,j,jacobianWeight]
    rw [dite_eq_left ⟨p.1.property.1,p.1.property.2⟩]
    ring
  let η := min ηj ηg
  have hη : 0 < η := lt_min hηj hηg
  have window : η ≤ J.window := (min_le_left _ _).trans wj
  let _ : MetricSpace M := LeanShared.BoundedRiemannianMetric.metric (E := E)
  have valueV (p : P) (x : M) : ‖v p x‖ ≤ Bw := by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (values (g p x) (mem_univ _)).trans (le_max_right _ _))) hBw
  let Hv := Cw*(Lg : ℝ)^a
  let B := Bw*Bj/R
  let C := (Bw*Cj+Hv*Bj)/R
  refine ⟨η,hη,window,B,C,by dsimp [B]; positivity,by dsimp [C,Hv]; positivity,?_⟩
  intro ε hp hw control
  let p : P := ⟨⟨ε,hp,hw.trans window⟩,control⟩
  have jac := jacobian ε hp (hw.trans (min_le_left _ _)) (hw.trans window) control
  have glip := lipG ε hp (hw.trans (min_le_right _ _)) (hw.trans window) control
  change LipschitzWith Lg (g p) at glip
  have holderV (x y : M) : ‖v p x-v p y‖ ≤ Hv*dist x y^a := by
    have difference := holderW (g p x) (g p y)
    have maps := Real.rpow_le_rpow dist_nonneg (glip.dist_le_mul x y) ha.le
    rw [Real.mul_rpow Lg.coe_nonneg dist_nonneg] at maps
    have estimate := (abs_max_sub_max_le_abs (w (g p x)) (w (g p y)) 0).trans
      (difference.trans (mul_le_mul_of_nonneg_left maps hCw))
    simpa only [Real.norm_eq_abs,Hv,mul_assoc] using estimate
  have valueJ (x : M) : ‖j p x‖ ≤ Bj := by simpa only [Real.norm_eq_abs] using jac.1 x
  have holderJ (x y : M) : ‖j p x-j p y‖ ≤ Cj*dist x y^a := by simpa only [Real.norm_eq_abs] using jac.2 x y
  have increment := LeanShared.FiniteSmoothReferenceCharts.product_increment univ (v p) (j p)
    Bw Bj Hv Cj a hBw (fun x _ => valueV p x) (fun x _ => valueJ x)
    (fun x _ y _ => holderV x y) (fun x _ y _ => holderJ x y)
  refine ⟨?_,?_⟩
  · intro x
    change |ψ p x| ≤ B
    rw [formula,abs_div,abs_mul,abs_of_pos hR]
    apply div_le_div_of_nonneg_right _ hR.le
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using valueV p x)
      (jac.1 x) (abs_nonneg _) hBw
  · intro x y
    change |ψ p x-ψ p y| ≤ C*dist x y^a
    rw [formula,formula,←sub_div,abs_div,abs_of_pos hR]
    have actual := increment x (mem_univ x) y (mem_univ y)
    have divided := div_le_div_of_nonneg_right actual hR.le
    rw [Real.norm_eq_abs] at divided
    exact divided.trans_eq (by dsimp [C]; ring)

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
