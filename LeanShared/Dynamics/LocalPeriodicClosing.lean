module
public import LeanShared.Dynamics.ForwardHyperbolicSequences
public import LeanShared.Analysis.LocalLipschitzRadialExtension
public import LeanShared.Dynamics.CyclicHyperbolicDeterminant

/-! Closing maps near a hyperbolic periodic orbit. Local maps `H_i` with `H_i 0 = 0`
and derivatives `δ`-close to split hyperbolic linear maps `A_i × B_i` on the
`r`-ball are composed along one period: `Φ_n = H_{n-1} ∘ ⋯ ∘ H_0`, and the closing map
`F w = Φ_n w - w`. On the set `R` of points whose orbit segment stays in the `r`-ball,
`F` is injective, orbit segments are bounded by `(C+1) ‖F w‖`, and every small defect
`b` is attained by a point of `R`. The proofs use forced periodic orbits of the radially
extended Lyapunov–Perron contraction. -/
public noncomputable section
set_option linter.unusedSectionVars false
open scoped NNReal
open Set
namespace LeanShared.LocalPeriodicClosing

variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]

/-- Periodic local hyperbolic data along one periodic orbit. -/
structure Data (U S : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] where
  A : ℤ → U ≃L[ℝ] U
  B : ℤ → S →L[ℝ] S
  H : ℤ → U × S → U × S
  H' : ℤ → U × S → (U × S) →L[ℝ] (U × S)
  k : ℝ≥0
  δ : ℝ≥0
  small : k + δ * 2 < 1
  inverse : ∀ i, ‖(A i).symm.toContinuousLinearMap‖ ≤ k
  stable : ∀ i, ‖B i‖ ≤ k
  r : ℝ
  r_pos : 0 < r
  zero : ∀ i, H i 0 = 0
  derivative : ∀ i w, ‖w‖ ≤ r → HasFDerivAt (H i) (H' i w) w
  derivative_zero : ∀ i, H' i 0 = (A i : U →L[ℝ] U).prodMap (B i)
  close : ∀ i w, ‖w‖ ≤ r → ‖H' i w - (A i : U →L[ℝ] U).prodMap (B i)‖ ≤ δ
  continuous : ∀ i, Continuous (H i)
  period : ℕ
  period_pos : 0 < period
  periodic_A : ∀ i, A (i + period) = A i
  periodic_B : ∀ i, B (i + period) = B i
  periodic_H : ∀ i, H (i + period) = H i
  periodic_H' : ∀ i, H' (i + period) = H' i

namespace Data

variable (d : Data U S)

/-- The split linear part. -/
@[expose] def D (i : ℤ) : (U × S) →L[ℝ] (U × S) := (d.A i : U →L[ℝ] U).prodMap (d.B i)

/-- Orbit segments. -/
@[expose] def orbit (m : ℕ) (w : U × S) : U × S :=
  Nat.rec (motive := fun _ => U × S) w (fun j x => d.H j x) m

theorem orbit_zero (w : U × S) : d.orbit 0 w = w := rfl

theorem orbit_succ (m : ℕ) (w : U × S) : d.orbit (m + 1) w = d.H m (d.orbit m w) := rfl

/-- The closing map. -/
@[expose] def closing (w : U × S) : U × S := d.orbit d.period w - w

/-- Points whose orbit segment stays in the `r`-ball. -/
@[expose] def region : Set (U × S) := {w | ∀ m ≤ d.period, ‖d.orbit m w‖ ≤ d.r}

/-- The radially extended nonlinear remainder. -/
@[expose] def extended (i : ℤ) : U × S → U × S :=
  RadialBallRetraction.extend d.r (fun w => d.H i w - d.D i w)

theorem extended_eq (i : ℤ) (w : U × S) (hw : ‖w‖ ≤ d.r) :
    d.extended i w = d.H i w - d.D i w :=
  RadialBallRetraction.extend_eq d.r d.r_pos _ hw

theorem extended_zero (i : ℤ) : d.extended i 0 = 0 := by
  rw [d.extended_eq i 0 (by rw [norm_zero]; exact d.r_pos.le), d.zero, map_zero, sub_zero]

theorem extended_lipschitz (i : ℤ) : LipschitzWith (d.δ * 2) (d.extended i) := by
  apply RadialBallRetraction.lipschitz_extend_of_fderiv d.r d.r_pos _ d.δ
  · intro w hw
    have hw' : ‖w‖ ≤ d.r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    exact ((d.derivative i w hw').sub (d.D i).hasFDerivAt).differentiableAt
  · intro w hw
    have hw' : ‖w‖ ≤ d.r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hd : HasFDerivAt (fun w => d.H i w - d.D i w) (d.H' i w - d.D i) w :=
      (d.derivative i w hw').sub (d.D i).hasFDerivAt
    rw [hd.fderiv]
    exact d.close i w hw'

theorem periodic_extended (i : ℤ) : d.extended (i + d.period) = d.extended i := by
  simp only [extended, D, d.periodic_H, d.periodic_A, d.periodic_B]

/-- The forcing with defect `b` at the last site of each period. -/
@[expose] def forcing (b : U × S) (i : ℤ) : U × S :=
  if i % d.period = (d.period : ℤ) - 1 then -b else 0

theorem periodic_forcing (b : U × S) (i : ℤ) : d.forcing b (i + d.period) = d.forcing b i := by
  simp only [forcing, Int.add_emod_right]

theorem norm_forcing (b : U × S) (i : ℤ) : ‖d.forcing b i‖ ≤ ‖b‖ := by
  simp only [forcing]
  split_ifs <;> simp

/-- The Green constant. -/
@[expose] def constant : ℝ := ((d.k : ℝ) + 1) / (1 - (d.k + d.δ * 2 : ℝ≥0))

theorem constant_nonneg : 0 ≤ d.constant := by
  have : ((d.k + d.δ * 2 : ℝ≥0) : ℝ) < 1 := by exact_mod_cast d.small
  exact div_nonneg (by positivity) (by linarith)

theorem step_eq (b : U × S) (i : ℤ) (w : U × S) (hw : ‖w‖ ≤ d.r) :
    ForwardHyperbolicSequences.step d.A d.B (fun i w => d.extended i w + d.forcing b i) i w =
      d.H i w + d.forcing b i := by
  have e := d.extended_eq i w hw
  simp only [ForwardHyperbolicSequences.step, e]
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_sub, D, ContinuousLinearMap.coe_prodMap', Prod.map_fst,
      ContinuousLinearEquiv.coe_coe]
    abel
  · simp only [Prod.snd_add, Prod.snd_sub, D, ContinuousLinearMap.coe_prodMap', Prod.map_snd]
    abel

/-- The forced periodic orbit with defect `b`. -/
theorem forced (b : U × S) :
    ∃ W : ℤ → U × S,
      (∀ i, W (i + 1) = ForwardHyperbolicSequences.step d.A d.B
        (fun i w => d.extended i w + d.forcing b i) i (W i)) ∧
      (∀ i, ‖W i‖ ≤ d.constant * ‖b‖) ∧
      (∀ i, W (i + d.period) = W i) ∧
      ∀ W' : ℤ → U × S, (∀ i, ‖W' i‖ ≤ d.r) →
        (∀ i, W' (i + 1) = d.H i (W' i) + d.forcing b i) → W' = W := by
  have lipschitz (i : ℤ) : LipschitzWith (d.δ * 2) (fun w => d.extended i w + d.forcing b i) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_add_right]
      exact (d.extended_lipschitz i).dist_le_mul x y
  obtain ⟨W, equation, bound, unique⟩ := ForwardHyperbolicSequences.exists_unique d.A d.B
    (fun i w => d.extended i w + d.forcing b i) d.k (d.δ * 2) d.small
    (fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (d.inverse i))
    (fun i => ContinuousLinearMap.lipschitzWith_of_opNorm_le (d.stable i)) lipschitz ‖b‖
    (fun i => by rw [d.extended_zero, zero_add]; exact d.norm_forcing b i)
  have bound' (i : ℤ) : ‖W i‖ ≤ d.constant * ‖b‖ := by
    rw [constant, div_mul_eq_mul_div]
    exact bound i
  refine ⟨W, equation, bound', ?_, ?_⟩
  · intro i
    have shifted := unique (fun j => W (j + d.period)) ⟨_, fun j => bound' (j + d.period)⟩
      (fun j => by
        have h := equation (j + d.period)
        rw [show j + d.period + 1 = j + 1 + d.period by ring] at h
        rw [h]
        simp only [ForwardHyperbolicSequences.step, d.periodic_A, d.periodic_B,
          d.periodic_extended, d.periodic_forcing])
    exact congrFun shifted i
  · intro W' small' eq'
    apply unique W' ⟨d.r, small'⟩
    intro i
    rw [eq' i, d.step_eq b i (W' i) (small' i)]

/-- The periodic sequence of an orbit segment. -/
@[expose] def sequence (w : U × S) (i : ℤ) : U × S := d.orbit (i % d.period).toNat w

theorem periodic_H_emod (i : ℤ) : d.H (i % d.period) = d.H i :=
  CyclicHyperbolicDeterminant.periodic_emod d.H d.period d.periodic_H i

theorem sequence_equation (w : U × S) (i : ℤ) :
    d.sequence w (i + 1) = d.H i (d.sequence w i) + d.forcing (d.closing w) i := by
  have hn' : (0 : ℤ) < d.period := by exact_mod_cast d.period_pos
  have r0 : 0 ≤ i % d.period := Int.emod_nonneg i hn'.ne'
  have r1 : i % d.period < d.period := Int.emod_lt_of_pos i hn'
  have decomposition := Int.emod_add_mul_ediv i d.period
  rcases lt_or_eq_of_le (show i % d.period + 1 ≤ d.period by omega) with lt | eq
  · have next : (i + 1) % d.period = i % d.period + 1 := by
      rw [show i + 1 = (i % d.period + 1) + d.period * (i / d.period) by omega,
        Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) lt]
    have noForce : d.forcing (d.closing w) i = 0 := by
      simp only [forcing]
      rw [ite_eq_right_iff]
      intro h
      omega
    rw [noForce, add_zero]
    simp only [sequence, next]
    rw [show (i % d.period + 1).toNat = (i % d.period).toNat + 1 by omega, orbit_succ,
      show (((i % d.period).toNat : ℕ) : ℤ) = i % d.period by omega, d.periodic_H_emod i]
  · have next : (i + 1) % d.period = 0 := by
      rw [show i + 1 = d.period * (i / d.period + 1) by rw [mul_add, mul_one]; omega]
      exact Int.mul_emod_right _ _
    have force : d.forcing (d.closing w) i = -d.closing w := by
      have h : i % d.period = (d.period : ℤ) - 1 := by omega
      simp only [forcing, h, ↓reduceIte]
    rw [force]
    simp only [sequence, next, Int.toNat_zero, orbit_zero]
    have last : (i % d.period).toNat + 1 = d.period := by omega
    have value : d.H i (d.orbit (i % d.period).toNat w) = d.orbit d.period w := by
      have step := (d.orbit_succ (i % d.period).toNat w).symm
      rw [show (((i % d.period).toNat : ℕ) : ℤ) = i % d.period by omega, d.periodic_H_emod i,
        last] at step
      exact step
    rw [value, closing]
    abel

theorem sequence_small (w : U × S) (hw : w ∈ d.region) (i : ℤ) : ‖d.sequence w i‖ ≤ d.r := by
  have hn' : (0 : ℤ) < d.period := by exact_mod_cast d.period_pos
  have r0 := Int.emod_nonneg i hn'.ne'
  have r1 := Int.emod_lt_of_pos i hn'
  exact hw _ (by omega)

/-- The closing map is injective on the region. -/
theorem injOn : InjOn d.closing d.region := by
  intro w hw w' hw' same
  obtain ⟨W, _, _, _, unique⟩ := d.forced (d.closing w)
  have first := unique (d.sequence w) (d.sequence_small w hw) (d.sequence_equation w)
  have second := unique (d.sequence w') (d.sequence_small w' hw') (fun i => by
    rw [d.sequence_equation w' i, same])
  have := congrFun (first.trans second.symm) 0
  simpa only [sequence, Int.zero_emod, Int.toNat_zero, orbit_zero] using this

/-- Orbit segments in the region are controlled by the closing defect. -/
theorem orbit_bound (w : U × S) (hw : w ∈ d.region) (m : ℕ) (hm : m ≤ d.period) :
    ‖d.orbit m w‖ ≤ (d.constant + 1) * ‖d.closing w‖ := by
  obtain ⟨W, _, bound, _, unique⟩ := d.forced (d.closing w)
  have same := unique (d.sequence w) (d.sequence_small w hw) (d.sequence_equation w)
  rcases lt_or_eq_of_le hm with lt | eq
  · have value : d.sequence w m = d.orbit m w := by
      simp only [sequence]
      rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast lt)]
      simp only [Int.toNat_natCast]
    rw [← value, same]
    exact (bound m).trans (by nlinarith [norm_nonneg (d.closing w), d.constant_nonneg])
  · rw [eq]
    have identity : d.orbit d.period w = w + d.closing w := by rw [closing]; abel
    have w0 : ‖w‖ ≤ d.constant * ‖d.closing w‖ := by
      have value : w = W 0 := by
        have := congrFun same 0
        simpa only [sequence, Int.zero_emod, Int.toNat_zero, orbit_zero] using this
      have hb := bound 0
      rwa [← value] at hb
    rw [identity]
    calc ‖w + d.closing w‖ ≤ ‖w‖ + ‖d.closing w‖ := norm_add_le _ _
      _ ≤ d.constant * ‖d.closing w‖ + ‖d.closing w‖ := by linarith
      _ = (d.constant + 1) * ‖d.closing w‖ := by ring

/-- Every small defect is attained in the region. -/
theorem exists_preimage (b : U × S) (hb : (d.constant + 1) * ‖b‖ ≤ d.r) :
    ∃ w ∈ d.region, d.closing w = b := by
  obtain ⟨W, equation, bound, periodic, _⟩ := d.forced b
  have small (i : ℤ) : ‖W i‖ ≤ d.r :=
    (bound i).trans (by nlinarith [norm_nonneg b, d.constant_nonneg])
  have true (i : ℤ) : W (i + 1) = d.H i (W i) + d.forcing b i := by
    rw [equation i, d.step_eq b i (W i) (small i)]
  have along : ∀ m : ℕ, m < d.period → d.orbit m (W 0) = W m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [orbit_succ, ih (by omega)]
      have h := true m
      have noForce : d.forcing b m = 0 := by
        simp only [forcing]
        rw [ite_eq_right_iff]
        intro h'
        rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast (show m < d.period by omega))] at h'
        omega
      rw [noForce, add_zero] at h
      push_cast
      exact h.symm
  have last : d.orbit d.period (W 0) = W 0 + b := by
    obtain ⟨p, hp⟩ : ∃ p, d.period = p + 1 := ⟨d.period - 1, by have := d.period_pos; omega⟩
    have hp' : p < d.period := by omega
    rw [hp, orbit_succ, along p hp']
    have h := true p
    have force : d.forcing b p = -b := by
      have h : (p : ℤ) % d.period = (d.period : ℤ) - 1 := by
        rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hp')]
        omega
      simp only [forcing, h, ↓reduceIte]
    rw [force] at h
    have wrap : W ((p : ℤ) + 1) = W 0 := by
      have := periodic 0
      rw [zero_add] at this
      rw [← this, hp]
      push_cast
      rfl
    rw [wrap] at h
    rw [h]
    abel
  refine ⟨W 0, fun m hm => ?_, by rw [closing, last]; abel⟩
  rcases lt_or_eq_of_le hm with lt | eq
  · rw [along m lt]
    exact small m
  · rw [eq, last]
    calc ‖W 0 + b‖ ≤ ‖W 0‖ + ‖b‖ := norm_add_le _ _
      _ ≤ d.constant * ‖b‖ + ‖b‖ := by linarith [bound 0]
      _ = (d.constant + 1) * ‖b‖ := by ring
      _ ≤ d.r := hb

end Data
end LeanShared.LocalPeriodicClosing
