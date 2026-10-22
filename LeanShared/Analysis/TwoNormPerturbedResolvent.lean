module

public import LeanShared.Analysis.UniformWeakResolventBound
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual inversion under weak-norm perturbations, by the two-norm
resolvent absorption argument. No perturbative spectral theorem is assumed. -/

public section
open ContinuousLinearMap Filter Topology
namespace LeanShared.TwoNormPerturbedResolvent
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A weak-resolvent estimate and a Peetre estimate absorb a small weak
perturbation, giving an actual bounded inverse and an explicit uniform bound.
Residual spectrum is the sole qualitative spectral premise. -/
theorem invertible (P Q : E →L[ℂ] E) (i : E →L[ℂ] W) (z : ℂ)
    (hQ : z ∈ resolventSet ℂ Q) (A B L η C J τ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hη : 0 ≤ η) (hC : 0 ≤ C)
    (normQ : ‖resolvent Q z‖ ≤ L)
    (weakQ : ∀ x, ‖i ((resolvent Q z) x)‖ ≤ η * ‖x‖ + C * ‖i x‖)
    (peetre : ∀ x, ‖x‖ ≤ A * ‖i x‖ + B * ‖(z • (1 : E →L[ℂ] E) - P) x‖)
    (strongPerturbation : ‖P - Q‖ ≤ J)
    (weakPerturbation : ‖i.comp (P - Q)‖ ≤ τ)
    (small : A * (η * J + C * τ) < 1)
    (noResidual : Function.Injective (z • (1 : E →L[ℂ] E) - P) →
      DenseRange (z • (1 : E →L[ℂ] E) - P)) :
    z ∈ resolventSet ℂ P ∧
      ‖resolvent P z‖ ≤ (A * ‖i‖ * L + B) / (1 - A * (η * J + C * τ)) := by
  let S := z • (1 : E →L[ℂ] E) - P
  let Δ := P - Q
  let κ := (A * ‖i‖ * L + B) / (1 - A * (η * J + C * τ))
  have gap : 0 < 1 - A * (η * J + C * τ) := sub_pos.mpr small
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have weakBound (x : E) : ‖i x‖ ≤ ‖i‖ * L * ‖S x‖ + (η * J + C * τ) * ‖x‖ := by
    have inverse : resolvent Q z * (z • (1 : E →L[ℂ] E) - Q) = 1 :=
      Ring.inverse_mul_cancel _ hQ
    have identity : x = (resolvent Q z) (S x) + (resolvent Q z) (Δ x) := by
      have hh := congrArg (fun T : E →L[ℂ] E => T x) inverse
      change (resolvent Q z) ((z • (1 : E →L[ℂ] E) - Q) x) = x at hh
      calc
        x = (resolvent Q z) ((z • (1 : E →L[ℂ] E) - Q) x) := hh.symm
        _ = (resolvent Q z) (S x + Δ x) := by
          congr 1
          change z • x - Q x = (z • x - P x) + (P x - Q x)
          abel
        _ = _ := map_add _ _ _
    have first : ‖i ((resolvent Q z) (S x))‖ ≤ ‖i‖ * L * ‖S x‖ := by
      calc
        _ ≤ ‖i‖ * ‖(resolvent Q z) (S x)‖ := i.le_opNorm _
        _ ≤ ‖i‖ * (‖resolvent Q z‖ * ‖S x‖) :=
          mul_le_mul_of_nonneg_left ((resolvent Q z).le_opNorm _) (norm_nonneg i)
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left normQ (norm_nonneg i)) (norm_nonneg _)
    have deltaStrong : ‖Δ x‖ ≤ J * ‖x‖ := (Δ.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right strongPerturbation (norm_nonneg x))
    have deltaWeak : ‖i (Δ x)‖ ≤ τ * ‖x‖ := ((i.comp Δ).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right weakPerturbation (norm_nonneg x))
    have second : ‖i ((resolvent Q z) (Δ x))‖ ≤ (η * J + C * τ) * ‖x‖ :=
      (weakQ (Δ x)).trans ((add_le_add
        (mul_le_mul_of_nonneg_left deltaStrong hη)
        (mul_le_mul_of_nonneg_left deltaWeak hC)).trans_eq (by ring))
    calc
      _ = ‖i ((resolvent Q z) (S x)) + i ((resolvent Q z) (Δ x))‖ := by
        conv_lhs => rw [identity, map_add]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add first second)
  have bound (x : E) : ‖x‖ ≤ κ * ‖S x‖ := by
    have h := (peetre x).trans (add_le_add
      (mul_le_mul_of_nonneg_left (weakBound x) hA) (le_refl (B * ‖S x‖)))
    change ‖x‖ ≤ ((A * ‖i‖ * L + B) / (1 - A * (η * J + C * τ))) * ‖S x‖
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ gap).mpr
    nlinarith
  have anti : ∃ K, AntilipschitzWith K S := by
    rw [antilipschitzWith_iff_exists_mul_le_norm]
    refine ⟨(κ + 1)⁻¹, by positivity, fun x => ?_⟩
    rw [inv_mul_eq_div, div_le_iff₀ (by positivity : 0 < κ + 1)]
    nlinarith [bound x, norm_nonneg (S x)]
  obtain ⟨Kanti, hanti⟩ := anti
  have dense : DenseRange S := noResidual hanti.injective
  have closed : IsClosed (Set.range S) := hanti.isClosed_range S.uniformContinuous
  have surj : Function.Surjective S := by
    intro y
    have hy := dense y
    rw [closed.closure_eq] at hy
    exact hy
  have hP : z ∈ resolventSet ℂ P :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hanti.injective, surj⟩
  refine ⟨hP, ContinuousLinearMap.opNorm_le_bound _ hκ fun x => ?_⟩
  have right : S * resolvent P z = 1 := Ring.mul_inverse_cancel _ hP
  have evaluate := congrArg (fun T : E →L[ℂ] E => T x) right
  change S ((resolvent P z) x) = x at evaluate
  simpa only [evaluate] using bound ((resolvent P z) x)

end LeanShared.TwoNormPerturbedResolvent
