module

public import LeanShared.Dynamics.SymbolicPastReset

/-! The literal one-sided graph system obtained by restricting bilateral
admissible paths.  Keeping admitted futures avoids adding transient
symbols that have no admissible past.  The canonical past reset supplies
an actual continuous section of the restriction map.
-/

public noncomputable section
namespace LeanShared.BilateralShadowingCoding
open Set Function
variable {A : Type*} {R : A → A → Prop}

@[expose] def FuturePath (R : A → A → Prop) : Type _ :=
  {a : ℕ → A // ∃ b : Path R, ∀ n : ℕ, b.val n = a n}

@[expose] def futureRestriction (a : Path R) : FuturePath R :=
  ⟨fun n => a.val n, a, fun _ => rfl⟩

@[expose] def futureExtension (a : FuturePath R) : Path R :=
  pastReset (Classical.choose a.property)

theorem futureExtension_future (a : FuturePath R) (n : ℕ) :
    (futureExtension a).val n = a.val n := by
  rw [futureExtension, pastReset_future _ _ (by omega)]
  exact Classical.choose_spec a.property n

theorem futureRestriction_extension (a : FuturePath R) :
    futureRestriction (futureExtension a) = a := by
  apply Subtype.ext
  funext n
  exact futureExtension_future a n

theorem futureExtension_restriction (a : Path R) :
    futureExtension (futureRestriction a) = pastReset a := by
  apply pastReset_eq_of_future
  intro n nonnegative
  have identity : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg nonnegative
  rw [← identity]
  exact Classical.choose_spec (futureRestriction a).property n.toNat

theorem futureRestriction_surjective : Surjective (futureRestriction : Path R → FuturePath R) :=
  fun a => ⟨futureExtension a, futureRestriction_extension a⟩

theorem futurePath_edge (a : FuturePath R) (n : ℕ) : R (a.val n) (a.val (n + 1)) := by
  rw [← futureExtension_future a n, ← futureExtension_future a (n + 1)]
  simpa only [Int.natCast_add, Int.cast_ofNat_Int] using (futureExtension a).property (n : ℤ)

variable [TopologicalSpace A]

@[expose] def futureShift (a : FuturePath R) : FuturePath R :=
  ⟨fun n => a.val (n + 1), shift R (futureExtension a), fun n => by
    change (futureExtension a).val ((n : ℤ) + 1) = a.val (n + 1)
    simpa only [Int.natCast_add, Int.cast_ofNat_Int] using futureExtension_future a (n + 1)⟩

@[simp] theorem futureShift_val (a : FuturePath R) (n : ℕ) :
    (futureShift a).val n = a.val (n + 1) := rfl

theorem futureRestriction_shift (a : Path R) :
    futureRestriction (shift R a) = futureShift (futureRestriction a) := by
  apply Subtype.ext
  funext n
  change a.val ((n : ℤ) + 1) = a.val (n + 1 : ℕ)
  simp only [Int.natCast_add, Int.cast_ofNat_Int]

@[expose] def PrefixAgreement (a b : FuturePath R) (radius : ℕ) : Prop :=
  ∀ n : ℕ, n ≤ radius → a.val n = b.val n

omit [TopologicalSpace A] in
theorem futureExtension_window (a b : FuturePath R) (radius : ℕ)
    (same : PrefixAgreement a b radius) :
    WindowAgreement (futureExtension a) (futureExtension b) radius := by
  let aa := Classical.choose a.property
  let bb := Classical.choose b.property
  have atZero : aa.val 0 = bb.val 0 := by
    rw [show aa.val 0 = a.val 0 from Classical.choose_spec a.property 0,
      show bb.val 0 = b.val 0 from Classical.choose_spec b.property 0]
    exact same 0 (by omega)
  have references := referencePath_congr (aa.val 0) (bb.val 0) ⟨aa, rfl⟩ ⟨bb, rfl⟩ atZero
  intro n lower upper
  by_cases negative : n < 0
  · change (pastReset aa).val n = (pastReset bb).val n
    rw [pastReset_past aa n negative, pastReset_past bb n negative, references]
  · have identity : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
    rw [← identity, futureExtension_future, futureExtension_future]
    exact same n.toNat (by omega)

instance : TopologicalSpace (FuturePath R) := inferInstanceAs
  (TopologicalSpace {a : ℕ → A // ∃ b : Path R, ∀ n : ℕ, b.val n = a n})

theorem futureRestriction_continuous : Continuous (futureRestriction : Path R → FuturePath R) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun n => (continuous_apply (n : ℤ)).comp continuous_subtype_val)

instance [DiscreteTopology A] [CompactSpace A] : CompactSpace (FuturePath R) :=
  futureRestriction_surjective.compactSpace futureRestriction_continuous

theorem futureShift_continuous : Continuous (futureShift : FuturePath R → FuturePath R) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun n => (continuous_apply (n + 1)).comp continuous_subtype_val)

theorem futureExtension_continuous [DiscreteTopology A] :
    Continuous (futureExtension : FuturePath R → Path R) := by
  let admitted := {i : A // ∃ a : Path R, a.val 0 = i}
  let symbol : FuturePath R → admitted := fun a =>
    ⟨a.val 0, futureExtension a, futureExtension_future a 0⟩
  have symbolContinuous : Continuous symbol :=
    ((continuous_apply 0).comp continuous_subtype_val).subtype_mk _
  let reference : admitted → Path R := fun i => referencePath i.val i.property
  have referenceContinuous : Continuous reference := continuous_of_discreteTopology
  have values : Continuous (fun a : FuturePath R => (futureExtension a).val) := by
    apply continuous_pi
    intro n
    by_cases negative : n < 0
    · have coordinate := (continuous_apply n).comp
        (continuous_subtype_val.comp (referenceContinuous.comp symbolContinuous))
      have identity (a : FuturePath R) : (futureExtension a).val n = (reference (symbol a)).val n := by
        rw [futureExtension, pastReset_past _ _ negative]
        have zero := Classical.choose_spec a.property 0
        exact congrArg (fun c : Path R => c.val n)
          (referencePath_congr _ _ _ _ zero)
      change Continuous (fun a : FuturePath R => (reference (symbol a)).val n) at coordinate
      simpa only [identity] using coordinate
    · have identity (a : FuturePath R) : (futureExtension a).val n = a.val n.toNat := by
        have cast : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
        calc
          _ = (futureExtension a).val (n.toNat : ℤ) := congrArg (futureExtension a).val cast.symm
          _ = a.val n.toNat := futureExtension_future a n.toNat
      simp only [identity]
      exact (continuous_apply n.toNat).comp continuous_subtype_val
  exact values.subtype_mk _

end LeanShared.BilateralShadowingCoding
