module
public import LeanShared.Dynamics.EntireOrbitIdentity
public import LeanShared.Dynamics.FinitePseudoOrbitErrors
public import LeanShared.Dynamics.FiniteIterateUniformity
import Mathlib.Tactic.Ring

/-! Bilateral shadowing for a fixed positive iterate implies one-step
bilateral shadowing. All interpolation and pseudo-orbit tolerances follow
from compactness and continuity; no shadowing at intermediate times is assumed. -/
public noncomputable section
namespace LeanShared.IterateShadowingTransfer
open Set Function BilateralHomeomorphismOrbit

set_option maxHeartbeats 1200000 in
theorem one_step
    {X:Type*} [MetricSpace X] [CompactSpace X] (T:X≃ₜX) (K:Set X)
    (N:ℕ) (positiveN:0<N)
    (blocks:∀ε:ℝ,0<ε → ∃η:ℝ,0<η ∧ ∀reference:ℤ→K,
      (∀n,dist ((T^N) (reference (n+1)).val) (reference n).val<η) →
      ∃p:ℤ→X,(∀n,(T^N) (p (n+1))=p n) ∧ ∀n,dist (p n) (reference n).val<ε)
    (ε:ℝ) (positiveε:0<ε) :
    ∃η:ℝ,0<η ∧ ∀reference:ℤ→K,
      (∀n,dist (T (reference (n+1)).val) (reference n).val<η) →
      ∃p:ℤ→X,(∀n,T (p (n+1))=p n) ∧ ∀n,dist (p n) (reference n).val<ε := by
  obtain ⟨α,positiveα,variation⟩ := FiniteIterateUniformity.exists_tolerance
    (T.symm:X→X) T.symm.continuous N (ε/2) (half_pos positiveε)
  obtain ⟨η0,positiveη0,shadow⟩ := blocks (α/2) (half_pos positiveα)
  obtain ⟨η,positiveη,errors⟩ := FinitePseudoOrbitErrors.exists_uniform_tolerance
    (T:X→X) T.continuous N (min η0 α) (lt_min positiveη0 positiveα)
  refine ⟨η,positiveη,fun reference step=>?_⟩
  have allErrors (m:ℤ) (j:ℕ) (hj:j≤N) :
      dist (((T:X→X)^[j]) (reference (m+(j:ℤ))).val) (reference m).val<min η0 α := by
    have finiteStep (i:ℕ) (_hi:i<N) :
        dist (T (reference (m+((i+1:ℕ):ℤ))).val) (reference (m+(i:ℤ))).val<η := by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using step (m+(i:ℤ))
    simpa only [Nat.cast_zero,add_zero] using
      errors (fun i=>(reference (m+(i:ℤ))).val) finiteStep j hj
  have blockStep (n:ℤ) :
      dist ((T^N) (reference ((n+1)*(N:ℤ))).val) (reference (n*(N:ℤ))).val<η0 := by
    have ix : (n+1)*(N:ℤ)=n*(N:ℤ)+(N:ℤ) := by ring
    simpa only [DiffeomorphismIterates.coe_pow,ix] using
      (allErrors (n*(N:ℤ)) N le_rfl).trans_le (min_le_left _ _)
  obtain ⟨p,pStep,pClose⟩ := shadow (fun n=>reference (n*(N:ℤ))) blockStep
  have canonical := eq_canonical (T^N) p pStep
  have blockPoint (n:ℤ) : p n=orbit T (p 0) (n*(N:ℤ)) :=
    (congrFun canonical n).trans (block_time T N (p 0) n)
  refine ⟨orbit T (p 0),fun n=>BilateralHomeomorphismOrbit.step T (p 0) n,fun m=>?_⟩
  let q := m/(N:ℤ)
  let r := (m%(N:ℤ)).toNat
  have nonnegative : 0≤m%(N:ℤ) := Int.emod_nonneg _ (by exact_mod_cast positiveN.ne')
  have less : m%(N:ℤ)<(N:ℤ) := Int.emod_lt_of_pos m (by exact_mod_cast positiveN)
  have castR : (r:ℤ)=m%(N:ℤ) := Int.toNat_of_nonneg nonnegative
  have rBound : r<N := by omega
  have decomp : m=q*(N:ℤ)+(r:ℤ) := by
    dsimp only [q]
    rw [castR]
    simpa only [mul_comm,add_comm] using (Int.emod_add_mul_ediv m (N:ℤ)).symm
  have value : orbit T (p 0) m=(T.symm:X→X)^[r] (p q) :=
    (congrArg (orbit T (p 0)) decomp).trans
      ((add_nat_time T (p 0) (q*(N:ℤ)) r).trans
        (congrArg ((T.symm:X→X)^[r]) (blockPoint q).symm))
  have first := variation (p q) (reference (q*(N:ℤ))).val
    ((pClose q).trans (half_lt_self positiveα)) r rBound.le
  have rawError := allErrors (q*(N:ℤ)) r rBound.le
  have point : reference (q*(N:ℤ)+(r:ℤ))=reference m := congrArg reference decomp.symm
  rw [point] at rawError
  have second := variation (((T:X→X)^[r]) (reference m).val) (reference (q*(N:ℤ))).val
    (rawError.trans_le (min_le_right _ _)) r rBound.le
  have cancel : ((T.symm:X→X)^[r]) (((T:X→X)^[r]) (reference m).val)=(reference m).val :=
    (Function.LeftInverse.iterate (fun x=>T.symm_apply_apply x) r) _
  rw [cancel] at second
  rw [value]
  have triangle := dist_triangle (((T.symm:X→X)^[r]) (p q))
    (((T.symm:X→X)^[r]) (reference (q*(N:ℤ))).val) (reference m).val
  rw [dist_comm (reference m).val] at second
  linarith

end LeanShared.IterateShadowingTransfer
