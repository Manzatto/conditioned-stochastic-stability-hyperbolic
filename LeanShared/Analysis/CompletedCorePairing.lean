module
public import LeanShared.Analysis.DyadicCompletion
public import Mathlib.Analysis.Normed.Operator.Extend

/-! A core pairing bounded in its actual core norm extends bilinearly to
the closure of that core. Tests need only their algebraic vector structure. -/
public noncomputable section
namespace LeanShared.CompletedCorePairing
variable {Core B Test : Type*}
  [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [AddCommGroup Test] [Module ℂ Test]
  (q : Core→ₗ[ℂ]B) (p : Core→ₗ[ℂ](Test→ₗ[ℂ]ℂ))
  (bounded : ∀ test, ∃ C : ℝ, ∀ f, ‖p f test‖ ≤ C*‖q f‖)

@[expose] def atTest (test : Test) : DyadicCompletion.closedCore q→L[ℂ]ℂ :=
  (p.flip test).extendOfNorm (DyadicCompletion.coreLift q)

include bounded in
theorem core (f : Core) (test : Test) :
    atTest q p test (DyadicCompletion.coreLift q f)=p f test :=
  LinearMap.extendOfNorm_eq (DyadicCompletion.coreLift_dense q) (bounded test) f

theorem bound (test : Test) (C : ℝ) (estimate : ∀ f, ‖p f test‖ ≤ C*‖q f‖)
    (z : DyadicCompletion.closedCore q) : ‖atTest q p test z‖ ≤ C*‖z‖ :=
  LinearMap.norm_extendOfNorm_apply_le (DyadicCompletion.coreLift_dense q) C estimate z

include bounded in
theorem add (f g : Test) (z : DyadicCompletion.closedCore q) :
    atTest q p (f+g) z=atTest q p f z+atTest q p g z := by
  refine (DyadicCompletion.coreLift_dense q).induction_on z
    (isClosed_eq (atTest q p (f+g)).continuous
      ((atTest q p f).continuous.add (atTest q p g).continuous)) ?_
  intro h
  rw [core q p bounded h (f+g),core q p bounded h f,core q p bounded h g,map_add]

include bounded in
theorem smul (c : ℂ) (f : Test) (z : DyadicCompletion.closedCore q) :
    atTest q p (c • f) z=c • atTest q p f z := by
  refine (DyadicCompletion.coreLift_dense q).induction_on z
    (isClosed_eq (atTest q p (c • f)).continuous
      ((atTest q p f).continuous.const_smul c)) ?_
  intro h
  rw [core q p bounded h (c • f),core q p bounded h f,map_smul]

@[expose] def pairing : DyadicCompletion.closedCore q→ₗ[ℂ](Test→ₗ[ℂ]ℂ) where
  toFun z := {
    toFun := fun test=>atTest q p test z
    map_add' := fun f g=>add q p bounded f g z
    map_smul' := fun c f=>smul q p bounded c f z }
  map_add' z w := by
    ext test
    exact (atTest q p test).map_add z w
  map_smul' c z := by
    ext test
    exact (atTest q p test).map_smul c z

theorem pairing_apply (z : DyadicCompletion.closedCore q) (test : Test) :
    pairing q p bounded z test=atTest q p test z := rfl

include bounded in
theorem pairing_core (f : Core) (test : Test) :
    pairing q p bounded (DyadicCompletion.coreLift q f) test=p f test :=
  core q p bounded f test
end LeanShared.CompletedCorePairing
