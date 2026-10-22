module
public import LeanShared.Analysis.RegularizedTraceFunctional

/-! The smoothing of a regularized trace family as a bounded operator, operator-norm bounds
from a dense core, and convergence of chart sums from local differences. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Filter MeasureTheory
open scoped Topology
namespace LeanShared.RegularizedTraceFunctional.Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

/-- The smoothing as a bounded operator. -/
@[expose] def smoothingCLM (F : Family E Y) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := F.smoothing
      map_add' := fun v w => by
        change ∫ y, F.test y (v + w) • F.vector y ∂F.measure =
          (∫ y, F.test y v • F.vector y ∂F.measure) + ∫ y, F.test y w • F.vector y ∂F.measure
        rw [← integral_add (F.integrable_smul v) (F.integrable_smul w)]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [map_add, add_smul]
      map_smul' := fun c v => by
        change ∫ y, F.test y (c • v) • F.vector y ∂F.measure =
          c • ∫ y, F.test y v • F.vector y ∂F.measure
        rw [← integral_smul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [map_smul, smul_eq_mul, mul_smul] }
    (∫ y, ‖F.test y‖ * ‖F.vector y‖ ∂F.measure) fun v => by
      change ‖∫ y, F.test y v • F.vector y ∂F.measure‖ ≤ _
      calc ‖∫ y, F.test y v • F.vector y ∂F.measure‖
          ≤ ∫ y, ‖v‖ * (‖F.test y‖ * ‖F.vector y‖) ∂F.measure := by
            refine norm_integral_le_of_norm_le (F.integrable.const_mul ‖v‖)
              (Eventually.of_forall fun y => ?_)
            rw [norm_smul]
            calc ‖F.test y v‖ * ‖F.vector y‖ ≤ ‖F.test y‖ * ‖v‖ * ‖F.vector y‖ :=
                  mul_le_mul_of_nonneg_right ((F.test y).le_opNorm v) (norm_nonneg _)
              _ = ‖v‖ * (‖F.test y‖ * ‖F.vector y‖) := by ring
        _ = (∫ y, ‖F.test y‖ * ‖F.vector y‖ ∂F.measure) * ‖v‖ := by
            rw [integral_const_mul, mul_comm]

theorem smoothingCLM_apply (F : Family E Y) (v : E) : F.smoothingCLM v = F.smoothing v := rfl

end LeanShared.RegularizedTraceFunctional.Family

namespace LeanShared.TraceFamilySmoothing

/-- An operator bounded on a dense range is bounded. -/
theorem opNorm_le_of_dense {C X : Type*} [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup X] [NormedSpace ℂ X] (T : X →L[ℂ] X) (κ : C →ₗ[ℂ] X)
    (dense : DenseRange κ) (K : ℝ) (hK : 0 ≤ K) (bound : ∀ c, ‖T (κ c)‖ ≤ K * ‖κ c‖) :
    ‖T‖ ≤ K := by
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun x => ?_
  exact dense.induction_on (p := fun x => ‖T x‖ ≤ K * ‖x‖) x
    (isClosed_le (T.continuous.norm) (continuous_const.mul continuous_norm)) bound

/-- Chart sums converge when their local differences do. -/
theorem sum_tendsto {ι X : Type*} [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℂ X]
    {L B : ι → Type*} [∀ k, AddCommGroup (L k)] [∀ k, Module ℂ (L k)]
    [∀ k, NormedAddCommGroup (B k)] [∀ k, NormedSpace ℂ (B k)]
    (P : X →L[ℂ] X) (Λ : ∀ k, L k →ₗ[ℂ] X) (N : ∀ k, L k →ₗ[ℂ] B k) (K : ι → ℝ)
    (hΛ : ∀ k h, ‖Λ k h‖ ≤ K k * ‖N k h‖) (F : ℕ → ∀ k, L k) (G : ∀ k, L k)
    (c : ι → ℝ) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (diff : ∀ n k, ‖N k (F n k - G k)‖ ≤ c k * r n) :
    Tendsto (fun n => ∑ k, P (Λ k (F n k))) atTop (𝓝 (∑ k, P (Λ k (G k)))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have total : Tendsto (fun n => ∑ k, ‖P‖ * (|K k| * (|c k| * |r n|))) atTop (𝓝 0) := by
    have each (k : ι) : Tendsto (fun n => ‖P‖ * (|K k| * (|c k| * |r n|))) atTop (𝓝 0) := by
      have h := ((hr.abs).const_mul |c k|).const_mul |K k| |>.const_mul ‖P‖
      simpa only [abs_zero, mul_zero] using h
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ fun k _ => each k
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) total
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [← map_sub, ← map_sub]
  calc ‖P (Λ k (F n k - G k))‖ ≤ ‖P‖ * ‖Λ k (F n k - G k)‖ := P.le_opNorm _
    _ ≤ ‖P‖ * (|K k| * (|c k| * |r n|)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖Λ k (F n k - G k)‖ ≤ K k * ‖N k (F n k - G k)‖ := hΛ k _
          _ ≤ |K k| * ‖N k (F n k - G k)‖ :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
          _ ≤ |K k| * (|c k| * |r n|) := by
              refine mul_le_mul_of_nonneg_left ((diff n k).trans ?_) (abs_nonneg _)
              rw [← abs_mul]; exact le_abs_self _

/-- A chart sum through a linear map and an operator. -/
theorem clm_lin_sum {ι C X : Type*} [Fintype ι] [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup X] [NormedSpace ℂ X] (P : X →L[ℂ] X) (G : C →ₗ[ℂ] X) (u : ι → C) :
    P (G (∑ k, u k)) = ∑ k, P (G (u k)) := by
  rw [map_sum, map_sum]

/-- Chart sums bounded by local norms. -/
theorem sum_bound {ι X : Type*} [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℂ X]
    {L B : ι → Type*} [∀ k, AddCommGroup (L k)] [∀ k, Module ℂ (L k)]
    [∀ k, NormedAddCommGroup (B k)] [∀ k, NormedSpace ℂ (B k)]
    (P : X →L[ℂ] X) (Λ : ∀ k, L k →ₗ[ℂ] X) (N : ∀ k, L k →ₗ[ℂ] B k) (K : ι → ℝ)
    (hΛ : ∀ k h, ‖Λ k h‖ ≤ K k * ‖N k h‖) (F : ∀ k, L k) (c : ι → ℝ) (x : ℝ)
    (hF : ∀ k, ‖N k (F k)‖ ≤ c k * x) (hx : 0 ≤ x) :
    ‖∑ k, P (Λ k (F k))‖ ≤ (‖P‖ * ∑ k, |K k| * |c k|) * x := by
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  calc ‖P (Λ k (F k))‖ ≤ ‖P‖ * ‖Λ k (F k)‖ := P.le_opNorm _
    _ ≤ ‖P‖ * (|K k| * (|c k| * x)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖Λ k (F k)‖ ≤ K k * ‖N k (F k)‖ := hΛ k _
          _ ≤ |K k| * ‖N k (F k)‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
          _ ≤ |K k| * (|c k| * x) :=
              mul_le_mul_of_nonneg_left ((hF k).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx))
                (abs_nonneg _)
    _ = ‖P‖ * (|K k| * |c k|) * x := by ring

end LeanShared.TraceFamilySmoothing
