module
public import ConditionedStochasticStabilityHyperbolic.Spectral.TraceDeterministicLeading
public import LeanShared.Analysis.TraceRatioCompare

/-! The deterministic leading record from trace asymptotics. If the regularized traces of `B^k =
(λ^{-N} T^N)^k` are `λ^{-N(k+1)}` times real traces that are relatively `η_j`-close to a
sequence `L` with `L(p)/λ^p → 1`, and `η_j → 0`, then `T` has a separated rank-one deterministic
leading projection at rate `λ`. -/
public noncomputable section
open Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [CompleteSpace E] in
/-- `(c T^N)^k (c T^{N-1} (T w)) = c^{k+1} T^{N(k+1)} w`. -/
theorem power_identity (T : E →L[ℂ] E) (c : ℂ) (N : ℕ) (hN : 0 < N) (k : ℕ) (w : E) :
    ((c • T ^ N) ^ k) ((c • T ^ (N - 1)) (T w)) = c ^ (k + 1) • T^[N * (k + 1)] w := by
  have step : (T ^ (N - 1)) (T w) = (T ^ N) w := by
    rw [← mul_apply_eq_comp, ← pow_succ, Nat.sub_add_cancel hN]
  rw [smul_pow, smul_apply, smul_apply, step, map_smul, ← mul_apply_eq_comp, ← pow_mul, ← pow_add,
    smul_smul, ← pow_succ, ← FunLike.coe_pow_eq_iterate, mul_add, mul_one]

omit [CompleteSpace E] in
/-- `c T^{N-1} (T w) = c T^N w`. -/
theorem step_identity (T : E →L[ℂ] E) (c : ℂ) (N : ℕ) (hN : 0 < N) (w : E) :
    (c • T ^ (N - 1)) (T w) = (c • T ^ N) w := by
  rw [smul_apply, smul_apply, ← mul_apply_eq_comp, ← pow_succ, Nat.sub_add_cancel hN]

theorem DeterministicLeading.of_trace_asymptotics (T : E →L[ℂ] E) (i : E →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (estimate : ∀ n x, ‖(T ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (lam : ℝ) (lam_pos : 0 < lam) (gap : α < lam)
    (radius : spectralRadius ℂ T ≤ ENNReal.ofReal lam)
    (positive : (lam : ℂ) ∈ spectrum ℂ T) (N : ℕ) (hN : 0 < N)
    {Y : Type*} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (F : ℕ → LeanShared.RegularizedTraceFunctional.Family E Y)
    (weak : ∀ v : E, ∀ φ : E →L[ℂ] ℂ, Tendsto (fun j => φ ((F j).smoothing v)) atTop
      (𝓝 (φ ((((lam : ℂ) ^ N)⁻¹ • T ^ (N - 1)) (T v)))))
    (tr : ℕ → ℕ → ℝ) (L : ℕ → ℝ) (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j)
    (ηlim : Tendsto η atTop (𝓝 0))
    (formula : ∀ j k, (F j).traceL ((((lam : ℂ) ^ N)⁻¹ • T ^ N) ^ k) =
      (((lam : ℂ) ^ N)⁻¹) ^ (k + 1) * (tr j (N * (k + 1)) : ℂ))
    (close : ∀ j k, |tr j (N * (k + 1)) - L (N * (k + 1))| ≤ η j * L (N * (k + 1)))
    (ratio : Tendsto (fun p => L p / lam ^ p) atTop (𝓝 1)) :
    ∃ d : DeterministicLeading T, d.rate = lam := by
  have growth : Tendsto (fun k : ℕ => N * (k + 1)) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left (k + 1) hN) (tendsto_add_atTop_nat 1)
  have ratio' : Tendsto (fun k : ℕ => L (N * (k + 1)) / lam ^ (N * (k + 1))) atTop (𝓝 1) :=
    ratio.comp growth
  have expand : ∀ j k, (F j).traceL ((((lam : ℂ) ^ N)⁻¹ • T ^ N) ^ k) =
      ((tr j (N * (k + 1)) / lam ^ (N * (k + 1)) : ℝ) : ℂ) := fun j k => by
    rw [formula, pow_mul]
    push_cast
    rw [inv_pow]
    ring
  have small : Tendsto (fun j => 2 * η j) atTop (𝓝 0) := by simpa using ηlim.const_mul 2
  exact DeterministicLeading.of_traces T i hi α R C D hα hR hC hD estimate lam lam_pos gap radius
    positive N hN F (fun v φ => by rw [← step_identity T _ N hN v]; exact weak v φ) _ (LeanShared.TraceRatioCompare.periodic L lam (fun k => N * (k + 1)) ratio')
    (fun j => 2 * η j) (LeanShared.TraceRatioCompare.compare
      (fun j k => (F j).traceL ((((lam : ℂ) ^ N)⁻¹ • T ^ N) ^ k)) tr L lam lam_pos
      (fun k => N * (k + 1)) η hη expand close ratio') small

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
