module
public import LeanShared.Analysis.CompletedCorePairing
public import LeanShared.Analysis.LpPointwiseLimitIdentification
public import Mathlib.Topology.Sequences

/-! Actual completed L1 blocks are recovered from their extended test pairing.
The recovery follows from smooth-core density and pointwise continuity of each
test evaluation; it does not assume a physical representation on the completion. -/
public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LeanShared.CompletedCorePairing
variable {Core B Test X : Type*}
  [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [AddCommGroup Test] [Module ℂ Test] [MeasurableSpace X]
  (q : Core→ₗ[ℂ]B) (p : Core→ₗ[ℂ](Test→ₗ[ℂ]ℂ))
  (bounded : ∀ test,∃ C:ℝ,∀ f,‖p f test‖≤C*‖q f‖)

theorem physical_block (μ : Measure X)
    (block : DyadicCompletion.closedCore q→L[ℂ]Lp ℂ 1 μ)
    (test : X→Test) (weight : ℂ)
    (coreFormula : ∀ f,block (DyadicCompletion.coreLift q f)=ᵐ[μ]
      (fun x=>weight*p f (test x))) (z : DyadicCompletion.closedCore q) :
    block z=ᵐ[μ](fun x=>weight*pairing q p bounded z (test x)) := by
  obtain ⟨sequence,members,converges⟩ :=
    mem_closure_iff_seq_limit.mp (DyadicCompletion.coreLift_dense q z)
  choose inputs inputEq using members
  have approximates : Tendsto (fun n=>DyadicCompletion.coreLift q (inputs n)) atTop (𝓝 z) := by
    simpa only [inputEq] using converges
  apply LpPointwiseLimitIdentification.identify μ
    (fun n=>block (DyadicCompletion.coreLift q (inputs n))) (block z)
    (fun n x=>weight*p (inputs n) (test x))
    (fun x=>weight*pairing q p bounded z (test x))
    (block.continuous.continuousAt.tendsto.comp approximates) (fun n=>coreFormula (inputs n))
  intro x
  have h := ((atTest q p (test x)).continuous.const_mul weight).continuousAt.tendsto.comp approximates
  simpa only [Function.comp_def,core q p bounded,pairing_apply] using h
end LeanShared.CompletedCorePairing
