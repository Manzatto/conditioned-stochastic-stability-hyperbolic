module

public import LeanShared.Dynamics.OneSidedCylinderPeriodicEquivalence
public import LeanShared.Dynamics.OneSidedIteratedPrehistoryFormula
public import LeanShared.Dynamics.ComplexOneSidedCylinderDiagonal

/-! The literal finite-cylinder diagonal is exactly the weighted finite
sum over actual matching-prefix inverse-orbit loops.  This is the
coefficient identity used before comparison to periodic orbit weights.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function ThermodynamicDefinitions
variable {A : Type*} [TopologicalSpace A] {R : A → A → Prop}

omit [TopologicalSpace A] in
theorem prefixAgreement_representative_iff (m : ℕ) (w : RealizedPrefix R m) (a : FuturePath R) :
    PrefixAgreement a (prefixRepresentative m w) m ↔ realizedPrefix m a = w := by
  constructor
  · intro same
    exact (realizedPrefix_eq_of_agreement m m le_rfl a (prefixRepresentative m w) same).trans
      (realizedPrefix_representative m w)
  · intro equal k bound
    have coordinate := congrArg (fun v : RealizedPrefix R m => v.val ⟨k, by omega⟩) equal
    change a.val k = w.val ⟨k, by omega⟩ at coordinate
    exact coordinate.trans (Classical.choose_spec w.property ⟨k, by omega⟩).symm

variable [DiscreteTopology A] [CompactSpace A] [Fintype A] [Nonempty (FuturePath R)]

omit [Nonempty (FuturePath R)] in
theorem complexCylinderPowerDiagonal_eq_loop_sum (ψ : C(FuturePath R, ℝ)) (m n : ℕ) :
    complexCylinderPowerDiagonal ψ m n =
      ∑ d : CylinderLoop (R := R) n m, (Real.exp (orbitSum futureShift ψ n d.val.2) : ℂ) := by
  classical
  have fiber (w : RealizedPrefix R m) :
      ((complexWeightedTransferOperator ψ) ^ n) (complexCylinderIndicator m w) (prefixRepresentative m w) =
      ∑ b : {b : FuturePrehistory n (prefixRepresentative m w) // PrefixAgreement b.val (prefixRepresentative m w) m},
        (Real.exp (orbitSum futureShift ψ n b.val.val) : ℂ) := by
    rw [complexWeightedTransferOperator_power_prehistory]
    let weight (b : FuturePrehistory n (prefixRepresentative m w)) : ℂ :=
      (Real.exp (orbitSum futureShift ψ n b.val) : ℂ)
    have changed :
        (∑ b : FuturePrehistory n (prefixRepresentative m w),
          (Real.exp (orbitSum futureShift ψ n b.val) : ℂ) * complexCylinderIndicator m w b.val) =
        ∑ b : FuturePrehistory n (prefixRepresentative m w),
          if PrefixAgreement b.val (prefixRepresentative m w) m then weight b else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      change weight b * (if realizedPrefix m b.val = w then (1 : ℂ) else 0) = _
      by_cases matching : PrefixAgreement b.val (prefixRepresentative m w) m
      · have word := (prefixAgreement_representative_iff m w b.val).mp matching
        rw [ite_eq_left word, ite_eq_left matching, mul_one]
      · have word : realizedPrefix m b.val ≠ w := by
          intro equal
          exact matching ((prefixAgreement_representative_iff m w b.val).mpr equal)
        rw [ite_eq_right word, ite_eq_right matching, mul_zero]
    rw [changed, ← Finset.sum_filter]
    exact Finset.sum_subtype _ (by intro b; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) weight
  have expansion : complexCylinderPowerDiagonal ψ m n =
      ∑ w : RealizedPrefix R m,
        ∑ b : {b : FuturePrehistory n (prefixRepresentative m w) // PrefixAgreement b.val (prefixRepresentative m w) m},
          (Real.exp (orbitSum futureShift ψ n b.val.val) : ℂ) := by
    exact Finset.sum_congr rfl (fun w _ => fiber w)
  rw [expansion]
  have flatten := Fintype.sum_sigma (fun d :
      (Σ w : RealizedPrefix R m, {b : FuturePrehistory n (prefixRepresentative m w) //
        PrefixAgreement b.val (prefixRepresentative m w) m}) =>
      (Real.exp (orbitSum futureShift ψ n d.2.val.val) : ℂ))
  rw [← flatten]
  symm
  apply Fintype.sum_equiv (cylinderLoopFiberEquiv n m)
  intro d
  rfl

@[expose] def cylinderLoopWeightSum (ψ : FuturePath R → ℝ) (n m : ℕ) : ℝ :=
  ∑ d : CylinderLoop (R := R) n m, Real.exp (orbitSum futureShift ψ n d.val.2)

omit [Nonempty (FuturePath R)] in
theorem complexCylinderPowerDiagonal_eq_real_loop_sum (ψ : C(FuturePath R, ℝ)) (m n : ℕ) :
    complexCylinderPowerDiagonal ψ m n = (cylinderLoopWeightSum ψ n m : ℂ) := by
  rw [complexCylinderPowerDiagonal_eq_loop_sum]
  exact (map_sum Complex.ofRealHom _ _).symm

end LeanShared.BilateralShadowingCoding
