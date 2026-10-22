module
public import LeanShared.Analysis.ClosedConeResolvent

/-! The positive real boundary point belongs to the spectrum. For a closed cone preserved by `P`, a
functional real and nonnegative on the cone, and a cone seed whose coefficients have the shifted
block growth at rate `e^P`, the number `e^P` is a spectral point when the radius is at most
`e^P`. If it were regular, a positive resolvent at some `0 < r < e^P` would give `0 ≤ ℓ(P^n x) ≤
t₀ r^{n+1}` through the recurrence `c_n = r t_n - t_{n+1}`, contradicting the growth. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology ENNReal
namespace LeanShared.PositiveBoundarySpectrum

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (C : Set H) (closed : IsClosed C) (zero : (0 : H) ∈ C)
  (add : ∀ {x y}, x ∈ C → y ∈ C → x + y ∈ C)
  (smul : ∀ (r : ℝ), 0 ≤ r → ∀ {x}, x ∈ C → (r : ℂ) • x ∈ C)

/-- The nonnegative recurrence bound. -/
theorem recurrence_bound (t c : ℕ → ℝ) (r : ℝ) (hr : 0 ≤ r) (ht : ∀ n, 0 ≤ t n)
    (hc : ∀ n, 0 ≤ c n) (identity : ∀ n, c n = r * t n - t (n + 1)) (n : ℕ) :
    c n ≤ t 0 * r ^ (n + 1) := by
  have tbound : ∀ n, t n ≤ t 0 * r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have step : t (n + 1) ≤ r * t n := by linarith [identity n, hc n]
      calc t (n + 1) ≤ r * t n := step
        _ ≤ r * (t 0 * r ^ n) := mul_le_mul_of_nonneg_left ih hr
        _ = t 0 * r ^ (n + 1) := by ring
  calc c n = r * t n - t (n + 1) := identity n
    _ ≤ r * t n := by linarith [ht (n + 1)]
    _ ≤ r * (t 0 * r ^ n) := mul_le_mul_of_nonneg_left (tbound n) hr
    _ = t 0 * r ^ (n + 1) := by ring

include closed zero add smul in
/-- The positive real boundary point belongs to the spectrum. -/
theorem mem_spectrum (P : H →L[ℂ] H) (positive : MapsTo P C C) (ℓ : H →L[ℂ] ℂ)
    (real : ∀ v ∈ C, ∃ t : ℝ, 0 ≤ t ∧ ℓ v = t) (x : H) (hx : x ∈ C) (Pexp : ℝ)
    (radius : spectralRadius ℂ P ≤ ENNReal.ofReal (Real.exp Pexp))
    (growth : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ ∃ K : ℝ, 0 < K ∧
      ∀ p : ℕ, 0 < p → Real.exp ((N * p : ℕ) * (Pexp - δ)) ≤
        K * ‖ℓ ((P ^ (N * p - 1)) x)‖) :
    ((Real.exp Pexp : ℝ) : ℂ) ∈ spectrum ℂ P := by
  by_contra notMem
  have regular : ((Real.exp Pexp : ℝ) : ℂ) ∈ resolventSet ℂ P := spectrum.notMem_iff.mp notMem
  have boundary := ClosedConeResolvent.mapsTo_at_regular_boundary C closed zero add smul P positive
    (Real.exp Pexp) (Real.exp_pos _) radius regular
  obtain ⟨r, hr0, hrlt, hrreg, hrmaps⟩ := ClosedConeResolvent.exists_lower_positive_resolvent C
    closed zero add smul P (Real.exp Pexp) (Real.exp_pos _) regular boundary
  set v := (resolvent P (r : ℂ) : H →L[ℂ] H) x with hv
  have vmem : v ∈ C := hrmaps hx
  -- the resolvent identity `r v - P v = x`
  have inverse : (algebraMap ℂ (H →L[ℂ] H) (r : ℂ) - P) v = x := by
    have unit : IsUnit (algebraMap ℂ (H →L[ℂ] H) (r : ℂ) - P) := hrreg
    exact congrArg (fun L : H →L[ℂ] H => L x) (Ring.mul_inverse_cancel _ unit)
  have Av : (algebraMap ℂ (H →L[ℂ] H) (r : ℂ) - P) v = (r : ℂ) • v - P v := by
    simp [Algebra.algebraMap_eq_smul_one]
  have stepIdentity (n : ℕ) : (P ^ n) x = (r : ℂ) • (P ^ n) v - (P ^ (n + 1)) v := by
    rw [← inverse, Av, map_sub, map_smul, pow_succ]
    rfl
  choose t ht hteq using fun n => real _ (ClosedConeResolvent.pow_mem C P positive vmem n)
  choose c hc hceq using fun n => real _ (ClosedConeResolvent.pow_mem C P positive hx n)
  have identity (n : ℕ) : c n = r * t n - t (n + 1) := by
    have h := congrArg ℓ (stepIdentity n)
    rw [map_sub, map_smul, hceq, hteq, hteq, smul_eq_mul] at h
    exact_mod_cast h
  have bound (n : ℕ) : ‖ℓ ((P ^ n) x)‖ ≤ t 0 * r ^ (n + 1) := by
    rw [hceq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc n)]
    exact recurrence_bound t c r hr0.le ht hc identity n
  -- choose a growth rate strictly above `r`
  have hlog : Real.log r < Pexp := by
    rw [Real.log_lt_iff_lt_exp hr0]
    exact hrlt
  set δ := (Pexp - Real.log r) / 2 with hδ
  have δpos : 0 < δ := by rw [hδ]; linarith
  obtain ⟨N, hN, K, hK, lower⟩ := growth δ δpos
  set s := Real.exp (Pexp - δ) with hs
  have rs : r < s := by
    rw [hs, ← Real.exp_log hr0]
    exact Real.exp_lt_exp.mpr (by rw [hδ]; linarith)
  have ratio : 1 < s / r := (one_lt_div hr0).mpr rs
  have ineq (p : ℕ) (hp : 0 < p) : (s / r) ^ (N * p) ≤ K * t 0 := by
    have hpos : 0 < N * p := Nat.mul_pos hN hp
    have hle := lower p hp
    have hb := bound (N * p - 1)
    rw [Nat.sub_add_cancel hpos] at hb
    have hexp : Real.exp ((N * p : ℕ) * (Pexp - δ)) = s ^ (N * p) := by
      rw [hs, ← Real.exp_nat_mul]
    rw [hexp] at hle
    have : s ^ (N * p) ≤ K * t 0 * r ^ (N * p) := by
      calc s ^ (N * p) ≤ K * ‖ℓ ((P ^ (N * p - 1)) x)‖ := hle
        _ ≤ K * (t 0 * r ^ (N * p)) := mul_le_mul_of_nonneg_left hb hK.le
        _ = K * t 0 * r ^ (N * p) := by ring
    rw [div_pow, div_le_iff₀ (pow_pos hr0 _)]
    exact this
  have unbounded := tendsto_pow_atTop_atTop_of_one_lt ratio
  obtain ⟨p0, hp0⟩ := (unbounded.eventually_gt_atTop (K * t 0)).exists_forall_of_atTop
  have big := hp0 (N * (p0 + 1)) (by nlinarith)
  exact absurd (ineq (p0 + 1) (Nat.succ_pos _)) (not_le.mpr big)

end LeanShared.PositiveBoundarySpectrum
