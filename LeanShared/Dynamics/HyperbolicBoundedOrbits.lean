module

public import LeanShared.Dynamics.HyperbolicTangentBlockEquivalences
public import LeanShared.Dynamics.HyperbolicInverseTangentBlocks
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Stable and unstable tangent spaces are exactly the vectors with bounded
forward and backward actual derivative orbits. No bounded-orbit
characterization is assumed as a source. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff Bundle
namespace LeanShared.HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
  [RiemannianBundle (TangentSpace (𝓘(ℝ,E)) : M → Type _)]
  {T : M ≃ₜ M} {Λ : Set M}

theorem HyperbolicData.mem_stable_of_bounded (k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) (hx : x ∈ Λ)
    (v : TangentSpace (𝓘(ℝ,E)) x) (orbitBound : ℝ)
    (bounded : ∀ n : ℕ, ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T : M → M)^[n]) x v‖ ≤ orbitBound) :
    v ∈ k.stable x := by
  let C := max orbitBound 0
  have Cnonnegative : 0 ≤ C := le_max_right _ _
  let s : k.stable x := ⟨k.projection x v, by
    rw [←k.projection_range x hx]
    exact LinearMap.mem_range.mpr ⟨v,rfl⟩⟩
  have idem : k.projection x (k.projection x v)=k.projection x v :=
    congrArg (fun A : TangentSpace (𝓘(ℝ,E)) x →L[ℝ] TangentSpace (𝓘(ℝ,E)) x => A v)
      (k.projection_idempotent x hx)
  let u : k.unstable x := ⟨v-k.projection x v,by
    rw [←k.projection_kernel x hx]
    change k.projection x (v-k.projection x v)=0
    rw [map_sub,idem,sub_self]⟩
  have parts : v=s.val+u.val := by dsimp [s,u]; abel
  let R := C+‖s‖
  have Bnonnegative : 0 ≤ R := add_nonneg Cnonnegative (norm_nonneg _)
  have zero : ‖u‖=0 := by
    by_contra nonzero
    have positive : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm nonzero)
    let κ := min 1 (‖u‖/(R+1))
    have κpositive : 0 < κ := lt_min zero_lt_one (div_pos positive (by linarith))
    have κone : κ ≤ 1 := min_le_left _ _
    have κbound : κ*(R+1) ≤ ‖u‖ := (le_div_iff₀ (by linarith : 0 < R+1)).mp (min_le_right _ _)
    obtain ⟨N,_,blocks⟩ := k.exists_actual_tangent_blocks forward inverse κ κpositive
    obtain ⟨S,U,stableNorm,inverseNorm,stableAction,unstableAction,_⟩ := blocks x hx
    let D := mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T^N : M ≃ₜ M) : M → M) x
    have vbound : ‖D v‖ ≤ C := by
      have estimate := bounded N
      rw [←DiffeomorphismIterates.coe_pow T N] at estimate
      exact estimate.trans (le_max_left _ _)
    have image : (U u).val=D v-(S s).val := by
      rw [unstableAction,stableAction]
      change D u.val=D v-D s.val
      conv_rhs => rw [parts,map_add]
      abel
    have stableBound : ‖S s‖ ≤ κ*‖s‖ :=
      (S.toContinuousLinearMap.le_opNorm s).trans
        (mul_le_mul_of_nonneg_right stableNorm (norm_nonneg _))
    have imageBound : ‖U u‖ ≤ R := by
      change ‖(U u).val‖ ≤ R
      rw [image]
      have triangle := norm_sub_le (D v) (S s).val
      have shrink : κ*‖s‖ ≤ ‖s‖ := by nlinarith [norm_nonneg s]
      dsimp [R]
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

theorem HyperbolicData.mem_unstable_of_bounded (k : HyperbolicData (E := E) T Λ)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverse : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm) (x : M) (hx : x ∈ Λ)
    (v : TangentSpace (𝓘(ℝ,E)) x) (orbitBound : ℝ)
    (bounded : ∀ n : ℕ, ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm : M → M)^[n]) x v‖ ≤ orbitBound) :
    v ∈ k.unstable x := by
  let C := max orbitBound 0
  have Cnonnegative : 0 ≤ C := le_max_right _ _
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
  let R := C+‖s‖
  have Bnonnegative : 0 ≤ R := add_nonneg Cnonnegative (norm_nonneg _)
  have zero : ‖u‖=0 := by
    by_contra nonzero
    have positive : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm nonzero)
    let κ := min 1 (‖u‖/(R+1))
    have κpositive : 0 < κ := lt_min zero_lt_one (div_pos positive (by linarith))
    have κone : κ ≤ 1 := min_le_left _ _
    have κbound : κ*(R+1) ≤ ‖u‖ := (le_div_iff₀ (by linarith : 0 < R+1)).mp (min_le_right _ _)
    obtain ⟨N,_,blocks⟩ := k.exists_actual_inverse_tangent_blocks forward inverse κ κpositive
    obtain ⟨S,U,stableNorm,inverseNorm,stableAction,unstableAction,_⟩ := blocks x hx
    let D := mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm^N : M ≃ₜ M) : M → M) x
    have vbound : ‖D v‖ ≤ C := by
      have estimate := bounded N
      rw [←DiffeomorphismIterates.coe_pow T.symm N] at estimate
      exact estimate.trans (le_max_left _ _)
    have image : (U u).val=D v-(S s).val := by
      rw [unstableAction,stableAction]
      change D u.val=D v-D s.val
      conv_rhs => rw [parts,map_add]
      abel
    have stableBound : ‖S s‖ ≤ κ*‖s‖ :=
      (S.toContinuousLinearMap.le_opNorm s).trans
        (mul_le_mul_of_nonneg_right stableNorm (norm_nonneg _))
    have imageBound : ‖U u‖ ≤ R := by
      change ‖(U u).val‖ ≤ R
      rw [image]
      have triangle := norm_sub_le (D v) (S s).val
      have shrink : κ*‖s‖ ≤ ‖s‖ := by nlinarith [norm_nonneg s]
      dsimp [R]
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

end LeanShared.HyperbolicBasicSet
