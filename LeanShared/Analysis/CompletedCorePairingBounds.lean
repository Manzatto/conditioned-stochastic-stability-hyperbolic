module
public import LeanShared.Analysis.CompletedCorePairing

/-! Quantitative bounds for the constructed completed core pairing. -/
public noncomputable section
namespace LeanShared.CompletedCorePairing
variable {Core B Test : Type*}
  [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [AddCommGroup Test] [Module ℂ Test]
  (q : Core→ₗ[ℂ]B) (p : Core→ₗ[ℂ](Test→ₗ[ℂ]ℂ))
  (bounded : ∀ test, ∃ C : ℝ, ∀ f, ‖p f test‖ ≤ C*‖q f‖)

theorem pairing_bound (test : Test) (C : ℝ) (estimate : ∀ f, ‖p f test‖ ≤ C*‖q f‖)
    (z : DyadicCompletion.closedCore q) : ‖pairing q p bounded z test‖ ≤ C*‖z‖ :=
  bound q p test C estimate z

theorem pairing_order_bound (test : Test) (C J H : ℝ) (hC : 0≤C)
    (size : ℝ) (coreEstimate : ∀ f, ‖p f test‖ ≤ C*‖q f‖*size)
    (testEstimate : size ≤ J*H) (z : DyadicCompletion.closedCore q) :
    ‖pairing q p bounded z test‖ ≤ (C*J)*‖z‖*H := by
  have estimate := pairing_bound q p bounded test (C*size)
    (fun f=>(coreEstimate f).trans_eq (mul_right_comm _ _ _)) z
  calc
    _ ≤ (C*size)*‖z‖ := estimate
    _ = (C*‖z‖)*size := mul_right_comm _ _ _
    _ ≤ (C*‖z‖)*(J*H) := mul_le_mul_of_nonneg_left testEstimate
      (mul_nonneg hC (norm_nonneg z))
    _ = _ := by ring
end LeanShared.CompletedCorePairing
