module

public import LeanShared.Dynamics.OneSidedCylinderLoops

/-! A literal finite cylinder loop is equivalent to an actual periodic
future.  Both directions retain the complete cylinder and inverse-orbit
provenance; no fixed-point counting or trace identity is assumed.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

@[expose] def cylinderLoopPeriodicEquiv (n m : ℕ) (positiveN : 0 < n) :
    CylinderLoop (R := R) n m ≃ PeriodicFuture (R := R) n where
  toFun := cylinderLoopPeriodic n m positiveN
  invFun := periodicCylinderLoop n m
  left_inv d := by
    let p := cylinderLoopPeriodic n m positiveN d
    have periodicAgreement := cylinderLoopPeriodic_window n m positiveN d
    have loopAgreement := periodicCylinderLoop_window n m p
    have symbol : (periodicCylinderLoop n m p).val.1 = d.val.1 := by
      change realizedPrefix m p.val = d.val.1
      apply Subtype.ext
      funext k
      change p.val.val k.val = d.val.1.val k
      calc
        _ = d.val.2.val k.val := periodicAgreement k.val (by omega)
        _ = (prefixRepresentative m d.val.1).val k.val := d.property.2 k.val (by omega)
        _ = d.val.1.val k := Classical.choose_spec d.val.1.property k
    apply Subtype.ext
    apply Prod.ext symbol
    apply futurePath_eq_of_initial_tail n (periodicCylinderLoop n m p).val.2 d.val.2
    · intro k before
      exact (loopAgreement k (by omega)).trans (periodicAgreement k (by omega))
    · exact (periodicCylinderLoop n m p).property.1.trans
        ((congrArg (prefixRepresentative m) symbol).trans d.property.1.symm)
  right_inv p := by
    apply periodicFutureWord_injective n positiveN
    funext k
    change (cylinderLoopPeriodic n m positiveN (periodicCylinderLoop n m p)).val.val k.val = p.val.val k.val
    exact (cylinderLoopPeriodic_window n m positiveN (periodicCylinderLoop n m p) k.val (by omega)).trans
      (periodicCylinderLoop_window n m p k.val (by omega))

@[expose] def cylinderLoopFiberEquiv (n m : ℕ) :
    CylinderLoop (R := R) n m ≃
      (Σ w : RealizedPrefix R m, {b : FuturePrehistory n (prefixRepresentative m w) //
        PrefixAgreement b.val (prefixRepresentative m w) m}) where
  toFun d := ⟨d.val.1, ⟨⟨d.val.2, d.property.1⟩, d.property.2⟩⟩
  invFun d := ⟨(d.1, d.2.val.val), d.2.val.property, d.2.property⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv d := by
    rcases d with ⟨w, ⟨⟨b, tail⟩, matching⟩⟩
    rfl

end LeanShared.BilateralShadowingCoding
