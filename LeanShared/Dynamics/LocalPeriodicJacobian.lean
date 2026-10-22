module
public import LeanShared.Dynamics.LocalPeriodicClosing
public import LeanShared.Dynamics.HyperbolicConeCloseness
public import LeanShared.Dynamics.CyclicDeterminantTelescoping
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Algebra.Order.Field.GeomSum

/-! The Jacobian of the closing map near a hyperbolic periodic orbit. Orbit segments
in the region are exponentially close to the periodic orbit (cone argument), the closing
map has derivative `P_w - 1` with `P_w` the product of the derivatives along the segment,
and if the derivatives are `α`-Hölder at the periodic orbit then
`det(1 - P_w) = det(1 - P_0) R` with `|R - 1| ≤ c ‖F w‖^α`. The constants depend only
on the hyperbolicity, Hölder data and dimension, not on the period or the orbit. -/
public noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open Finset
namespace LeanShared.LocalPeriodicClosing.Data

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  (d : Data U S)

theorem k_add_δ_lt_one : (d.k : ℝ) + d.δ < 1 := by
  have := d.small
  have h : ((d.k + d.δ * 2 : ℝ≥0) : ℝ) < 1 := by exact_mod_cast this
  push_cast at h
  linarith [d.δ.coe_nonneg]

theorem nonlinear_small (i : ℤ) (v : U × S) (hv : ‖v‖ ≤ d.r) :
    ‖d.H i v - d.D i v‖ ≤ d.δ * ‖v‖ := by
  have lip : LipschitzOnWith d.δ (fun v => d.H i v - d.D i v) (Metric.closedBall 0 d.r) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) _ _ (convex_closedBall 0 d.r)
    · intro x hx
      have hx' : ‖x‖ ≤ d.r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      exact ((d.derivative i x hx').sub (d.D i).hasFDerivAt).differentiableAt
    · intro x hx
      have hx' : ‖x‖ ≤ d.r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      have hd : HasFDerivAt (fun w => d.H i w - d.D i w) (d.H' i x - d.D i) x :=
        (d.derivative i x hx').sub (d.D i).hasFDerivAt
      rw [hd.fderiv, ← NNReal.coe_le_coe, coe_nnnorm]
      exact d.close i x hx'
  have h := lip.dist_le_mul v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv) 0
    (by simpa only [Metric.mem_closedBall, dist_self] using d.r_pos.le)
  simpa only [d.zero, map_zero, sub_zero, dist_zero_right] using h

/-- Exponential closeness to the periodic orbit. -/
theorem closeness (w : U × S) (hw : w ∈ d.region) (m : ℕ) (hm : m ≤ d.period) :
    ‖d.orbit m w‖ ≤ (d.constant + 1) * ‖d.closing w‖ *
      (HyperbolicConeCloseness.rate d.k d.δ ^ m +
        HyperbolicConeCloseness.rate d.k d.δ ^ (d.period - m)) := by
  refine HyperbolicConeCloseness.closeness (fun m => d.A m) (fun m => d.B m) d.k d.δ
    d.k.coe_nonneg d.δ.coe_nonneg d.k_add_δ_lt_one (fun m => d.inverse m) (fun m => d.stable m)
    (fun m v => d.H m v - d.D m v) (fun m => d.orbit m w) d.period (fun m _ => ?_)
    (fun m hm' => d.nonlinear_small m _ (hw m hm'.le)) _ (fun m hm' => d.orbit_bound w hw m hm')
    m hm
  rw [orbit_succ]
  apply Prod.ext
  · simp only [Prod.fst_sub, D, ContinuousLinearMap.coe_prodMap', Prod.map_fst,
      ContinuousLinearEquiv.coe_coe]
    abel
  · simp only [Prod.snd_sub, D, ContinuousLinearMap.coe_prodMap', Prod.map_snd]
    abel

/-- The derivative sequence along an orbit segment. -/
@[expose] def derivatives (w : U × S) (i : ℤ) : (U × S) →L[ℝ] (U × S) :=
  d.H' i (d.orbit (i % d.period).toNat w)

theorem periodic_derivatives (w : U × S) (i : ℤ) :
    d.derivatives w (i + d.period) = d.derivatives w i := by
  simp only [derivatives, d.periodic_H', Int.add_emod_right]

theorem derivatives_apply (w : U × S) (m : ℕ) (hm : m < d.period) :
    d.derivatives w m = d.H' m (d.orbit m w) := by
  simp only [derivatives]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hm), Int.toNat_natCast]

theorem hasFDerivAt_orbit (w : U × S) (hw : w ∈ d.region) :
    ∀ m ≤ d.period, HasFDerivAt (d.orbit m)
      (CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 m) w := by
  intro m
  induction m with
  | zero => intro _; exact hasFDerivAt_id w
  | succ m ih =>
    intro hm
    have step := (d.derivative m (d.orbit m w) (hw m (by omega))).comp w (ih (by omega))
    rw [CyclicHyperbolicDeterminant.prodFrom_succ, zero_add, d.derivatives_apply w m (by omega)]
    exact step

theorem hasFDerivAt_closing (w : U × S) (hw : w ∈ d.region) :
    HasFDerivAt d.closing (CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period -
      ContinuousLinearMap.id ℝ (U × S)) w :=
  (d.hasFDerivAt_orbit w hw d.period le_rfl).sub (hasFDerivAt_id w)

theorem derivatives_zero : d.derivatives 0 = d.D := by
  funext i
  have orbit0 : ∀ m, d.orbit m (0 : U × S) = 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [orbit_succ, ih, d.zero]
  simp only [derivatives, orbit0, d.derivative_zero, D]

theorem exp_sub_one_le (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 2) : Real.exp t - 1 ≤ Real.exp 2 * t := by
  have lower : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have identity : Real.exp t - 1 = Real.exp t * (1 - Real.exp (-t)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [identity]
  calc Real.exp t * (1 - Real.exp (-t)) ≤ Real.exp t * t :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos t).le
    _ ≤ Real.exp 2 * t := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) h0

/-- One-site Hölder bound along the region. -/
theorem site_bound (K α : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1)
    (holder : ∀ i v, ‖v‖ ≤ d.r → ‖d.H' i v - d.D i‖ ≤ K * ‖v‖ ^ α)
    (w : U × S) (hw : w ∈ d.region) (i : ℕ) (hi : i < d.period) :
    ‖d.derivatives w i - d.D i‖ ≤ K * ((d.constant + 1) * ‖d.closing w‖) ^ α *
      ((HyperbolicConeCloseness.rate d.k d.δ ^ α) ^ i +
        (HyperbolicConeCloseness.rate d.k d.δ ^ α) ^ (d.period - i)) := by
  rw [d.derivatives_apply w i hi]
  set θ := HyperbolicConeCloseness.rate d.k d.δ
  have hθ : 0 ≤ θ := HyperbolicConeCloseness.rate_nonneg _ _ d.k.coe_nonneg d.δ.coe_nonneg
  have hc : 0 ≤ d.constant + 1 := by linarith [d.constant_nonneg]
  have hb : 0 ≤ (d.constant + 1) * ‖d.closing w‖ := mul_nonneg hc (norm_nonneg _)
  have base := d.closeness w hw i hi.le
  rw [mul_assoc]
  refine (holder i (d.orbit i w) (hw i hi.le)).trans (mul_le_mul_of_nonneg_left ?_ hK)
  calc ‖d.orbit i w‖ ^ α ≤ ((d.constant + 1) * ‖d.closing w‖ * (θ ^ i + θ ^ (d.period - i))) ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) base hα.le
    _ = ((d.constant + 1) * ‖d.closing w‖) ^ α * (θ ^ i + θ ^ (d.period - i)) ^ α :=
        Real.mul_rpow hb (by positivity)
    _ ≤ ((d.constant + 1) * ‖d.closing w‖) ^ α * ((θ ^ i) ^ α + (θ ^ (d.period - i)) ^ α) :=
        mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow (by positivity) (by positivity)
          hα.le hα1) (Real.rpow_nonneg hb _)
    _ = ((d.constant + 1) * ‖d.closing w‖) ^ α * ((θ ^ α) ^ i + (θ ^ α) ^ (d.period - i)) := by
        rw [← Real.rpow_natCast_mul hθ, ← Real.rpow_natCast_mul hθ, mul_comm (i : ℝ),
          mul_comm ((d.period - i : ℕ) : ℝ), Real.rpow_mul_natCast hθ, Real.rpow_mul_natCast hθ]

theorem geometric_two (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) (n : ℕ) :
    ∑ i ∈ range n, (q ^ i + q ^ (n - i)) ≤ 2 / (1 - q) := by
  have first : ∑ i ∈ range n, q ^ i ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) h0 h1
    rwa [← range_eq_Ico, pow_zero] at h
  have second : ∑ i ∈ range n, q ^ (n - i) ≤ ∑ i ∈ range n, q ^ (n - 1 - i) :=
    sum_le_sum fun i hi => pow_le_pow_of_le_one h0 h1.le (by
      have := mem_range.mp hi
      omega)
  rw [sum_range_reflect (fun i => q ^ i) n] at second
  rw [sum_add_distrib]
  calc _ ≤ 1 / (1 - q) + 1 / (1 - q) := add_le_add first (second.trans first)
    _ = 2 / (1 - q) := by ring

/-- Uniform Hölder control of the Lefschetz determinant along the region. -/
theorem det_comparison (k δ : ℝ≥0) (small : k + δ * 2 < 1) (K α : ℝ) (hK : 0 ≤ K)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ c ρ0 : ℝ, 0 < c ∧ 0 < ρ0 ∧ ∀ d : Data U S, d.k = k → d.δ = δ →
      (∀ i v, ‖v‖ ≤ d.r → ‖d.H' i v - d.D i‖ ≤ K * ‖v‖ ^ α) →
      ∀ w ∈ d.region, ‖d.closing w‖ ≤ ρ0 → ∃ R : ℝ,
        LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
          CyclicHyperbolicDeterminant.prodFrom (d.derivatives w) 0 d.period) :
            (U × S) →ₗ[ℝ] (U × S)) =
        LinearMap.det ((ContinuousLinearMap.id ℝ (U × S) -
          CyclicHyperbolicDeterminant.prodFrom d.D 0 d.period) : (U × S) →ₗ[ℝ] (U × S)) * R ∧
        |R - 1| ≤ c * ‖d.closing w‖ ^ α := by
  obtain ⟨L, rdet, hL, hrdet, ratio⟩ := CyclicHyperbolicDeterminant.det_ratio (U := U) (S := S)
  have small' : k + δ < 1 :=
    lt_of_le_of_lt (by rw [mul_two, ← add_assoc]; exact le_self_add) small
  have smallR : ((k + δ * 2 : ℝ≥0) : ℝ) < 1 := by exact_mod_cast small
  have smallR' : ((k + δ : ℝ≥0) : ℝ) < 1 := by exact_mod_cast small'
  set C : ℝ := ((k : ℝ) + 1) / (1 - (k + δ * 2 : ℝ≥0)) with hC
  set Cdet : ℝ := ((k : ℝ) + 1) / (1 - (k + δ : ℝ≥0)) with hCdet
  have hC0 : 0 ≤ C := div_nonneg (by positivity) (by linarith)
  have hCdet0 : 0 ≤ Cdet := div_nonneg (by positivity) (by linarith)
  set θ : ℝ := HyperbolicConeCloseness.rate k δ
  have hθ0 : 0 ≤ θ := HyperbolicConeCloseness.rate_nonneg _ _ k.coe_nonneg δ.coe_nonneg
  have hθ1 : θ < 1 := HyperbolicConeCloseness.rate_lt_one _ _ k.coe_nonneg δ.coe_nonneg (by
    have h : (((k + δ : ℝ≥0)) : ℝ) < 1 := smallR'
    push_cast at h
    exact h)
  set q : ℝ := θ ^ α
  have hq0 : 0 ≤ q := Real.rpow_nonneg hθ0 _
  have hq1 : q < 1 := Real.rpow_lt_one hθ0 hθ1 hα
  set A0 : ℝ := K * (C + 1) ^ α
  have hA0 : 0 ≤ A0 := mul_nonneg hK (Real.rpow_nonneg (by linarith) _)
  set c0 : ℝ := L * Cdet * A0 * (2 / (1 - q))
  have hc0 : 0 ≤ c0 := by
    have : 0 ≤ 2 / (1 - q) := div_nonneg (by norm_num) (by linarith)
    positivity
  set M : ℝ := 2 * A0 * Cdet / rdet + 4 * L * Cdet * A0 + c0
  have hM : 0 ≤ M := by
    have : 0 ≤ 2 * A0 * Cdet / rdet := div_nonneg (by positivity) hrdet.le
    positivity
  set ρ0 : ℝ := (1 / (M + 1)) ^ α⁻¹
  have hρ0 : 0 < ρ0 := Real.rpow_pos_of_pos (by positivity) _
  have hρ0α : ρ0 ^ α = 1 / (M + 1) := Real.rpow_inv_rpow (by positivity) hα.ne'
  refine ⟨2 * Real.exp 2 * c0 + 1, ρ0, by positivity, hρ0, ?_⟩
  intro d hk hδ holder w hw hb
  set b := d.closing w
  have hbα : ‖b‖ ^ α ≤ 1 / (M + 1) := hρ0α ▸ Real.rpow_le_rpow (norm_nonneg _) hb hα.le
  have constant_eq : d.constant = C := by simp only [constant, hk, hδ, hC]
  have rate_eq : HyperbolicConeCloseness.rate d.k d.δ = θ := by rw [hk, hδ]
  set E : ℤ → (U × S) →L[ℝ] (U × S) := fun i => d.derivatives w i - d.D i
  have periodicE (i : ℤ) : E (i + d.period) = E i := by
    simp only [E, d.periodic_derivatives, D, d.periodic_A, d.periodic_B]
  have scale : ((C + 1) * ‖b‖) ^ α = (C + 1) ^ α * ‖b‖ ^ α :=
    Real.mul_rpow (by linarith) (norm_nonneg _)
  have siteNat (i : ℕ) (hi : i < d.period) :
      ‖E i‖ ≤ A0 * ‖b‖ ^ α * (q ^ i + q ^ (d.period - i)) := by
    have h := d.site_bound K α hK hα hα1 holder w hw i hi
    rw [constant_eq, rate_eq, scale] at h
    simp only [E, A0]
    calc _ ≤ _ := h
      _ = K * (C + 1) ^ α * ‖b‖ ^ α * (q ^ i + q ^ (d.period - i)) := by ring
  have siteAll (i : ℤ) : ‖E i‖ ≤ A0 * ‖b‖ ^ α * 2 := by
    have hn' : (0 : ℤ) < d.period := by exact_mod_cast d.period_pos
    have r0 := Int.emod_nonneg i hn'.ne'
    have r1 := Int.emod_lt_of_pos i hn'
    have reduce : E i = E (((i % d.period).toNat : ℕ) : ℤ) := by
      rw [show (((i % d.period).toNat : ℕ) : ℤ) = i % d.period by omega]
      exact (CyclicHyperbolicDeterminant.periodic_emod E d.period periodicE i).symm
    rw [reduce]
    refine (siteNat _ (by omega)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have a1 : q ^ (i % d.period).toNat ≤ 1 := pow_le_one₀ hq0 hq1.le
    have a2 : q ^ (d.period - (i % d.period).toNat) ≤ 1 := pow_le_one₀ hq0 hq1.le
    linarith
  have hEδ (i : ℤ) : ‖E i‖ ≤ δ := by
    have hn' : (0 : ℤ) < d.period := by exact_mod_cast d.period_pos
    have r0 := Int.emod_nonneg i hn'.ne'
    have r1 := Int.emod_lt_of_pos i hn'
    rw [← hδ]
    exact d.close i _ (hw _ (by omega))
  have smallSite (i : ℤ) : Cdet * ‖E i‖ ≤ rdet := by
    have h1 : Cdet * ‖E i‖ ≤ Cdet * (A0 * ‖b‖ ^ α * 2) := mul_le_mul_of_nonneg_left (siteAll i) hCdet0
    have h2 : 2 * A0 * Cdet / rdet * ‖b‖ ^ α ≤ M * ‖b‖ ^ α := by
      have : 0 ≤ 4 * L * Cdet * A0 + c0 := by positivity
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    have h3 : M * ‖b‖ ^ α ≤ 1 := by
      calc M * ‖b‖ ^ α ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hbα hM
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
    have h4 : 2 * A0 * Cdet / rdet * ‖b‖ ^ α = Cdet * (A0 * ‖b‖ ^ α * 2) / rdet := by ring
    rw [h4, div_le_iff₀ hrdet] at h2
    nlinarith
  have smallSite' (i : ℤ) : L * (Cdet * ‖E i‖) ≤ 1 / 2 := by
    have h1 : L * (Cdet * ‖E i‖) ≤ L * (Cdet * (A0 * ‖b‖ ^ α * 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (siteAll i) hCdet0) hL.le
    have h3 : M * ‖b‖ ^ α ≤ 1 := by
      calc M * ‖b‖ ^ α ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hbα hM
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
    have h2 : 4 * L * Cdet * A0 * ‖b‖ ^ α ≤ M * ‖b‖ ^ α := by
      have : 0 ≤ 2 * A0 * Cdet / rdet + c0 := by
        have : 0 ≤ 2 * A0 * Cdet / rdet := div_nonneg (by positivity) hrdet.le
        positivity
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    nlinarith
  obtain ⟨R, equation, lower, upper⟩ := ratio d.A d.B E k δ small'
    (fun i => hk ▸ d.inverse i) (fun i => hk ▸ d.stable i) hEδ d.period d.period_pos
    d.periodic_A d.periodic_B periodicE smallSite smallSite'
  have sameM : (fun i => (d.A i : U →L[ℝ] U).prodMap (d.B i) + E i) = d.derivatives w := by
    funext i
    simp only [E, D, add_sub_cancel]
  rw [sameM] at equation
  refine ⟨R, equation, ?_⟩
  -- the exponent
  set X := ∑ i ∈ range d.period, L * (Cdet * ‖E i‖)
  have hX0 : 0 ≤ X := sum_nonneg fun i _ => by positivity
  have hX : X ≤ c0 * ‖b‖ ^ α := by
    calc X ≤ ∑ i ∈ range d.period, L * (Cdet * (A0 * ‖b‖ ^ α * (q ^ i + q ^ (d.period - i)))) :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (siteNat i (mem_range.mp hi)) hCdet0) hL.le
      _ = L * Cdet * A0 * ‖b‖ ^ α * ∑ i ∈ range d.period, (q ^ i + q ^ (d.period - i)) := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ => by ring
      _ ≤ L * Cdet * A0 * ‖b‖ ^ α * (2 / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geometric_two q hq0 hq1 _)
            (by have := Real.rpow_nonneg (norm_nonneg b) α; positivity)
      _ = c0 * ‖b‖ ^ α := by ring
  have hX1 : X ≤ 1 := by
    have : c0 * ‖b‖ ^ α ≤ M * ‖b‖ ^ α := by
      have : 0 ≤ 2 * A0 * Cdet / rdet + 4 * L * Cdet * A0 := by
        have : 0 ≤ 2 * A0 * Cdet / rdet := div_nonneg (by positivity) hrdet.le
        positivity
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
    have h3 : M * ‖b‖ ^ α ≤ 1 := by
      calc M * ‖b‖ ^ α ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hbα hM
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
    linarith
  have up : R - 1 ≤ Real.exp 2 * X :=
    (sub_le_sub_right upper 1).trans (exp_sub_one_le X hX0 (by linarith))
  have down : 1 - R ≤ 2 * X := by
    have := Real.add_one_le_exp (-(2 * X))
    linarith
  have e1 : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have ht : 0 ≤ ‖b‖ ^ α := Real.rpow_nonneg (norm_nonneg b) α
  have hc0t : 0 ≤ c0 * ‖b‖ ^ α := mul_nonneg hc0 ht
  have h1 : Real.exp 2 * X ≤ Real.exp 2 * (c0 * ‖b‖ ^ α) :=
    mul_le_mul_of_nonneg_left hX (Real.exp_pos 2).le
  have h2 : c0 * ‖b‖ ^ α ≤ Real.exp 2 * (c0 * ‖b‖ ^ α) := le_mul_of_one_le_left hc0t e1
  have h3 : (2 * Real.exp 2 * c0 + 1) * ‖b‖ ^ α =
      2 * (Real.exp 2 * (c0 * ‖b‖ ^ α)) + ‖b‖ ^ α := by ring
  rw [abs_le, h3]
  constructor
  · linarith
  · linarith

end LeanShared.LocalPeriodicClosing.Data
