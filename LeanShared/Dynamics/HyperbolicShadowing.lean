module
public import LeanShared.Dynamics.HyperbolicBackwardTransform
import Lean.Elab.Tactic.Omega

/-! A constructive nonautonomous hyperbolic shadowing primitive. For actual
split maps with small nonlinear derivative/Lipschitz bounds and a bounded
pseudo-orbit error, a bilateral Lyapunov--Perron contraction produces the
unique bounded entire orbit and an explicit shadowing bound. Adapted charts
for a manifold hyperbolic set are not assumed to have been constructed here. -/
public noncomputable section
namespace LeanShared.HyperbolicShadowing
open scoped NNReal BoundedContinuousFunction

structure Data (U S : Type*) [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup S] [NormedSpace ℝ S] where
  expanding : ℤ → U ≃L[ℝ] U
  contracting : ℤ → S →L[ℝ] S
  nonlinear : ℤ → U × S → U × S
  k : ℝ≥0
  δ : ℝ≥0
  small : k + δ < 1
  inverse_bound : ∀ n, LipschitzWith k (expanding n).symm
  stable_bound : ∀ n, LipschitzWith k (contracting n)
  nonlinear_bound : ∀ n, LipschitzWith δ (nonlinear n)
  error : ℝ
  nonlinear_zero : ∀ n, ‖nonlinear n 0‖ ≤ error

namespace Data
variable {U S : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem k_le_one (d : Data U S) : d.k ≤ 1 :=
  (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ d.δ from zero_le)).trans d.small.le

@[expose] def raw (d : Data U S) (z : ℤ → U × S) (n : ℤ) : U × S :=
  ((d.expanding (n - 1)).symm ((z (n - 1)).1 - (d.nonlinear (n - 1) (z n)).1),
    d.contracting n (z (n + 1)).2 + (d.nonlinear n (z (n + 1))).2)

theorem raw_distance (d : Data U S) (z w : ℤ → U × S)
    (D : ℝ) (distance : ∀ n, dist (z n) (w n) ≤ D) (n : ℤ) :
    dist (d.raw z n) (d.raw w n) ≤ (d.k + d.δ : ℝ≥0) * D := by
  let index : ℕ → ℤ := fun i => n - 1 + (i : ℤ)
  have zero : index 0 = n - 1 := by simp only [index, Nat.cast_zero, add_zero]
  have one : index 1 = n := by simp only [index, Nat.cast_one, sub_add_cancel]
  have two : index 2 = n + 1 := by dsimp [index]; omega
  have bound := HyperbolicBackwardTransform.raw_distance
    (fun i => (d.expanding (index i)).symm) (fun i => d.contracting (index i))
    (fun i => d.nonlinear (index i)) d.k d.δ d.k_le_one
    (fun i => d.inverse_bound (index i)) (fun i => d.stable_bound (index i))
    (fun i => d.nonlinear_bound (index i)) 0 (fun i => z (index i))
    (fun i => w (index i)) D (fun i => distance (index i)) 1
  simpa only [raw, HyperbolicBackwardTransform.raw, zero, one, two] using bound

theorem raw_zero_bound (d : Data U S) (n : ℤ) :
    ‖d.raw (fun _ => 0) n‖ ≤ ((d.k : ℝ) + 1) * d.error := by
  let index : ℕ → ℤ := fun i => n - 1 + (i : ℤ)
  have zero : index 0 = n - 1 := by simp only [index, Nat.cast_zero, add_zero]
  have one : index 1 = n := by simp only [index, Nat.cast_one, sub_add_cancel]
  have bound := HyperbolicBackwardTransform.raw_zero_bound
    (fun i => (d.expanding (index i)).symm) (fun i => d.contracting (index i))
    (fun i => d.nonlinear (index i)) d.k (fun i => d.inverse_bound (index i))
    (fun i => (d.expanding (index i)).symm.map_zero)
    (fun i => (d.contracting (index i)).map_zero) d.error
    (fun i => d.nonlinear_zero (index i)) 0 1
  have nonnegative : 0 ≤ ((d.k : ℝ) + 1) * d.error := mul_nonneg (by positivity)
    ((norm_nonneg _).trans (d.nonlinear_zero 0))
  simpa only [raw, HyperbolicBackwardTransform.raw, zero, one, norm_zero,
    max_eq_right nonnegative] using bound

@[expose] def transform (d : Data U S) (z : ℤ →ᵇ U × S) : ℤ →ᵇ U × S :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (d.raw z)
    (((d.k + d.δ : ℝ≥0) : ℝ) * ‖z‖ + ((d.k : ℝ) + 1) * d.error) fun n => by
      calc
        ‖d.raw z n‖ ≤ dist (d.raw z n) (d.raw (fun _ => 0) n) + ‖d.raw (fun _ => 0) n‖ := by
          simpa only [dist_zero_right] using dist_triangle (d.raw z n) (d.raw (fun _ => 0) n) 0
        _ ≤ _ := add_le_add (d.raw_distance z (fun _ => 0) ‖z‖
          (fun i => by simpa only [dist_zero_right] using z.norm_coe_le_norm i) n) (d.raw_zero_bound n)

theorem transform_contracting (d : Data U S) : ContractingWith (d.k + d.δ) d.transform := by
  refine ⟨d.small, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  apply (BoundedContinuousFunction.dist_le
    (mul_nonneg (d.k + d.δ).coe_nonneg dist_nonneg)).mpr
  exact fun n => d.raw_distance z w (dist z w)
    (fun i => BoundedContinuousFunction.dist_coe_le_dist i) n

@[expose] def orbit [CompleteSpace U] [CompleteSpace S] (d : Data U S) : ℤ →ᵇ U × S :=
  d.transform_contracting.fixedPoint d.transform

theorem orbit_raw [CompleteSpace U] [CompleteSpace S] (d : Data U S) (n : ℤ) :
    d.raw d.orbit n = d.orbit n :=
  congrArg (fun z : ℤ →ᵇ U × S => z n) d.transform_contracting.fixedPoint_isFixedPt

@[expose] def map (d : Data U S) (n : ℤ) (z : U × S) : U × S :=
  ((d.expanding n) z.1 + (d.nonlinear n z).1,
    (d.contracting n) z.2 + (d.nonlinear n z).2)

theorem orbit_step [CompleteSpace U] [CompleteSpace S] (d : Data U S) (n : ℤ) :
    d.map n (d.orbit (n + 1)) = d.orbit n := by
  have unstable := congrArg (d.expanding n) (congrArg Prod.fst (d.orbit_raw (n + 1)))
  have stable := congrArg Prod.snd (d.orbit_raw n)
  change (d.expanding n) ((d.expanding (n + 1 - 1)).symm _) = _ at unstable
  rw [add_sub_cancel_right, (d.expanding n).apply_symm_apply] at unstable
  apply Prod.ext
  · change (d.expanding n) (d.orbit (n + 1)).1 +
      (d.nonlinear n (d.orbit (n + 1))).1 = (d.orbit n).1
    rw [← unstable, sub_add_cancel]
  · exact stable

theorem orbit_unique [CompleteSpace U] [CompleteSpace S] (d : Data U S)
    (z : ℤ →ᵇ U × S) (step : ∀ n, d.map n (z (n + 1)) = z n) : z = d.orbit := by
  apply d.transform_contracting.fixedPoint_unique
  apply BoundedContinuousFunction.ext
  intro n
  apply Prod.ext
  · change (d.expanding (n - 1)).symm ((z (n - 1)).1 -
      (d.nonlinear (n - 1) (z n)).1) = (z n).1
    have unstable := congrArg Prod.fst (step (n - 1))
    change (d.expanding (n - 1)) (z (n - 1 + 1)).1 +
      (d.nonlinear (n - 1) (z (n - 1 + 1))).1 = (z (n - 1)).1 at unstable
    rw [sub_add_cancel] at unstable
    have rearranged := congrArg (d.expanding (n - 1)).symm (eq_sub_of_add_eq unstable)
    simpa only [(d.expanding (n - 1)).symm_apply_apply] using rearranged.symm
  · have stable := congrArg Prod.snd (step n)
    exact stable

theorem shadowing_bound [CompleteSpace U] [CompleteSpace S] (d : Data U S) :
    ‖d.orbit‖ ≤ (((d.k : ℝ) + 1) * d.error) / (1 - (d.k + d.δ : ℝ≥0)) := by
  have estimate := d.transform_contracting.dist_fixedPoint_le 0
  rw [dist_zero_left, dist_zero_left] at estimate
  apply estimate.trans
  apply div_le_div_of_nonneg_right _ d.transform_contracting.one_sub_K_pos.le
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (by positivity)
    ((norm_nonneg _).trans (d.nonlinear_zero 0)))).mpr
  exact d.raw_zero_bound

end Data
end LeanShared.HyperbolicShadowing
