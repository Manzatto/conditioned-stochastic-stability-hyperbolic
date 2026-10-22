module

public import LeanShared.Dynamics.HyperbolicInverseTangentBlocks
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! The actual unstable tangent subspace is determined uniquely by the
hyperbolic derivative bounds. The proof uses actual contracting tangent
blocks and rules out any nonzero stable component of an unstable vector. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (TangentSpace (𝓘(ℝ,E)) : M → Type _)]
  {T : M ≃ₜ M} {Λ : Set M}

private theorem unstable_le (h k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) (hx : x ∈ Λ) :
    h.unstable x ≤ k.unstable x := by
  intro v hv
  have idem : k.projection x (k.projection x v)=k.projection x v :=
    congrArg (fun A : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x => A v)
      (k.projection_idempotent x hx)
  let s : k.unstable x := ⟨v-k.projection x v,by
    rw [←k.projection_kernel x hx]
    change k.projection x (v-k.projection x v)=0
    rw [map_sub,idem,sub_self]⟩
  let u : k.stable x := ⟨k.projection x v, by
    rw [←k.projection_range x hx]
    exact LinearMap.mem_range.mpr ⟨v,rfl⟩⟩
  have parts : v=s.val+u.val := by dsimp [s,u]; abel
  let B := h.constant*‖v‖+‖s‖
  have Bnonnegative : 0 ≤ B := add_nonneg (mul_nonneg h.constant_pos.le (norm_nonneg _)) (norm_nonneg _)
  have zero : ‖u‖=0 := by
    by_contra nonzero
    have positive : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm nonzero)
    let κ := min 1 (‖u‖/(B+1))
    have κpositive : 0 < κ := lt_min zero_lt_one (div_pos positive (by linarith))
    have κone : κ ≤ 1 := min_le_left _ _
    have κbound : κ*(B+1) ≤ ‖u‖ := (le_div_iff₀ (by linarith : 0 < B+1)).mp (min_le_right _ _)
    obtain ⟨N,_,blocks⟩ := k.exists_actual_inverse_tangent_blocks forward inverse κ κpositive
    obtain ⟨S,U,stableNorm,inverseNorm,stableAction,unstableAction,_⟩ := blocks x hx
    let D := mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm^N : M ≃ₜ M) : M → M) x
    have vbound : ‖D v‖ ≤ h.constant*‖v‖ := by
      have estimate := h.unstable_bound N x hx v hv
      rw [←DiffeomorphismIterates.coe_pow T.symm N] at estimate
      exact estimate.trans (by
        have power := pow_le_one₀ h.contraction_pos.le h.contraction_lt_one.le (n := N)
        have left := mul_le_mul_of_nonneg_left power h.constant_pos.le
        simpa only [mul_one] using mul_le_mul_of_nonneg_right left (norm_nonneg v))
    have image : (U u).val=D v-(S s).val := by
      rw [unstableAction,stableAction]
      change D u.val=D v-D s.val
      conv_rhs => rw [parts,map_add]
      abel
    have stableBound : ‖S s‖ ≤ κ*‖s‖ :=
      (S.toContinuousLinearMap.le_opNorm s).trans
        (mul_le_mul_of_nonneg_right stableNorm (norm_nonneg _))
    have imageBound : ‖U u‖ ≤ B := by
      change ‖(U u).val‖ ≤ B
      rw [image]
      have triangle := norm_sub_le (D v) (S s).val
      have shrink : κ*‖s‖ ≤ ‖s‖ := by nlinarith [norm_nonneg s]
      dsimp [B]
      exact triangle.trans (add_le_add vbound (stableBound.trans shrink))
    have sourceBound : ‖u‖ ≤ κ*‖U u‖ := by
      have estimate := (U.symm.toContinuousLinearMap.le_opNorm (U u)).trans
        (mul_le_mul_of_nonneg_right inverseNorm (norm_nonneg (U u)))
      change ‖U.symm (U u)‖ ≤ κ*‖U u‖ at estimate
      rw [ContinuousLinearEquiv.symm_apply_apply] at estimate
      exact estimate
    have finalBound := sourceBound.trans (mul_le_mul_of_nonneg_left imageBound κpositive.le)
    nlinarith
  have uZero : u.val=0 := congrArg Subtype.val (norm_eq_zero.mp zero)
  have same : v=s.val := by rw [parts,uZero,add_zero]
  exact same ▸ s.property

theorem HyperbolicData.unstable_eq (h k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) (hx : x ∈ Λ) :
    h.unstable x=k.unstable x :=
  le_antisymm (unstable_le h k forward inverse x hx) (unstable_le k h forward inverse x hx)

end LeanShared.HyperbolicBasicSet
