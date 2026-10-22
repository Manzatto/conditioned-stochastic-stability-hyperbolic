module
public import LeanShared.Analysis.SmoothPartialDerivativeBounds
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Actual finite frequency jets of a fixed compact cutoff times a smooth
symbol have constructed uniform bounds and Lipschitz dependence on the
bounded finite-dimensional coefficient parameter, on all frequencies. -/
public noncomputable section
open Set Metric
open scoped ContDiff
namespace LeanShared.CompactFrequencyJetBounds
variable {A Z:Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

theorem exists_bounds (ψ:A × Z→ℂ) (smoothψ:ContDiff ℝ ∞ ψ)
    (χ:Z→ℂ) (smoothχ:ContDiff ℝ ∞ χ) (compactχ:HasCompactSupport χ)
    {D:ℝ} (hD:0≤D) (n:ℕ):
    ∃B L:ℝ,0≤B ∧ 0≤L ∧
      (∀a:A,‖a‖≤D→∀j≤n,∀z,
        ‖iteratedFDeriv ℝ j (fun w=>χ w*ψ (a,w)) z‖≤B) ∧
      ∀a a':A,‖a‖≤D→‖a'‖≤D→∀j≤n,∀z,
        ‖iteratedFDeriv ℝ j (fun w=>χ w*ψ (a,w)) z-
          iteratedFDeriv ℝ j (fun w=>χ w*ψ (a',w)) z‖≤L*‖a-a'‖:=by
  obtain ⟨R,hR,rbound⟩:=compactχ.isBounded.exists_pos_norm_le
  let Ψ:A × Z→ℂ:=fun p=>χ p.2*ψ p
  have smooth:ContDiff ℝ ∞ Ψ:=(smoothχ.comp contDiff_snd).mul smoothψ
  have member (a:A) (ha:‖a‖≤D) (z:Z) (hz:z∈tsupport χ):
      (a,z)∈closedBall (0:A × Z) (D+R):=by
    rw [mem_closedBall,dist_zero_right,Prod.norm_def]
    exact max_le (ha.trans (le_add_of_nonneg_right hR.le))
      ((rbound z hz).trans (le_add_of_nonneg_left hD))
  choose Bn Ln hBn hLn value lip using fun j:ℕ=>SmoothPartialDerivativeBounds.compact_bounds j Ψ smooth
    (isCompact_closedBall (0:A × Z) (D+R)) (convex_closedBall (0:A × Z) (D+R))
  let B:ℝ:=∑j∈Finset.range (n+1),Bn j
  let L:ℝ:=∑j∈Finset.range (n+1),Ln j
  have hB:0≤B:=Finset.sum_nonneg (fun j _=>hBn j)
  have hL:0≤L:=Finset.sum_nonneg (fun j _=>hLn j)
  have Ble (j:ℕ) (hj:j≤n):Bn j≤B:=
    Finset.single_le_sum (fun i _=>hBn i) (Finset.mem_range.mpr (by omega))
  have Lle (j:ℕ) (hj:j≤n):Ln j≤L:=
    Finset.single_le_sum (fun i _=>hLn i) (Finset.mem_range.mpr (by omega))
  have outside (a:A) (j:ℕ) (z:Z) (hz:z∉tsupport χ):
      iteratedFDeriv ℝ j (fun w=>χ w*ψ (a,w)) z=0:=by
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hz (tsupport_mul_subset_left (tsupport_iteratedFDeriv_subset j hh))
  refine ⟨B,L,hB,hL,?_,?_⟩
  · intro a ha j hj z
    by_cases hz:z∈tsupport χ
    · exact (value j (a,z) (member a ha z hz)).trans (Ble j hj)
    · rw [outside a j z hz,norm_zero]
      exact hB
  · intro a a' ha ha' j hj z
    by_cases hz:z∈tsupport χ
    · have raw:=lip j (a,z) (member a ha z hz) (a',z) (member a' ha' z hz)
      have estimate:‖iteratedFDeriv ℝ j (fun w=>χ w*ψ (a,w)) z-
          iteratedFDeriv ℝ j (fun w=>χ w*ψ (a',w)) z‖≤Ln j*‖a-a'‖:=by
        simpa only [SmoothPartialDerivativeBounds.frequencyDerivative,Ψ,Prod.sub_def,
          sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using raw
      exact estimate.trans (mul_le_mul_of_nonneg_right (Lle j hj) (norm_nonneg _))
    · rw [outside a j z hz,outside a' j z hz,sub_self,norm_zero]
      positivity
end LeanShared.CompactFrequencyJetBounds
