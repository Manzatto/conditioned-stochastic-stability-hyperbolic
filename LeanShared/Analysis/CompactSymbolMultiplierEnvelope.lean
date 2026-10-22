module
public import LeanShared.Analysis.SupportedJetFourierEvaluation
public import LeanShared.Analysis.SmoothPartialDerivativeBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-! Multiplication by an actual smooth frequency symbol preserves the
spatial polynomial envelope of the finite compatible jet, uniformly
over a compact coefficient parameter set. All derivative constants are
constructed, including when the jet is only finite-C^n. -/
public noncomputable section
open Set MeasureTheory
open scoped ContDiff FourierTransform
namespace LeanShared.CompactSymbolMultiplierEnvelope
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z:Type} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasurableSpace Z] [BorelSpace Z]

theorem exists_bound (ψ:V × Z→ℂ) (smooth:ContDiff ℝ ∞ ψ)
    {P:Set V} (compactP:IsCompact P) {K:Set Z} (compactK:IsCompact K) (n:ℕ):
    ∃C:ℝ,0≤C ∧∀p∈P,∀q:SupportedFiniteJetSpace.space n K,∀z,
      (1+‖z‖)^n*‖𝓕 (fun w=>ψ (p,w)*SupportedJetFourierEvaluation.physical n K q w) z‖≤C*‖q‖:=by
  have bounds (j:ℕ):∃B:ℝ,0≤B ∧∀p∈P,∀z∈K,
      ‖iteratedFDeriv ℝ j (fun w=>ψ (p,w)) z‖≤B:=by
    obtain ⟨B,hB,bound⟩:=((compactP.prod compactK).image
      (SmoothPartialDerivativeBounds.smooth_partial j ψ smooth).continuous).isBounded.exists_pos_norm_le
    exact ⟨B,hB.le,fun p hp z hz=>bound _
      (mem_image_of_mem _ (show (p,z)∈P ×ˢ K from ⟨hp,hz⟩))⟩
  choose B hB symbolBound using bounds
  let Qn (j:ℕ):ℝ:=∑i∈Finset.range (j+1),(j.choose i:ℝ)*B i
  have hQn (j:ℕ):0≤Qn j:=Finset.sum_nonneg (fun i _=>mul_nonneg (Nat.cast_nonneg _) (hB i))
  let Q:ℝ:=∑j∈Finset.range (n+1),Qn j
  have hQ:0≤Q:=Finset.sum_nonneg (fun j _=>hQn j)
  let C:ℝ:=4^n*((n+1:ℕ)*(Q*volume.real K))
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro p hp q z
  have fq:ContDiff ℝ (n:ℕ∞ω) (SupportedJetFourierEvaluation.physical n K q):=
    (BoundedFiniteJetSpace.construct n (F:=ℂ)).regular q.val
  have fs:ContDiff ℝ (n:ℕ∞ω) (fun w=>ψ (p,w)):=
    (smooth.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have supported:tsupport (fun w=>ψ (p,w)*SupportedJetFourierEvaluation.physical n K q w)⊆K:=
    tsupport_mul_subset_right.trans (SupportedFiniteJetSpace.tsupport_subset n compactK.isClosed q)
  have estimate (j:ℕ) (hj:j≤n) (w:Z) (hw:w∈K):
      ‖iteratedFDeriv ℝ j (fun w=>ψ (p,w)*SupportedJetFourierEvaluation.physical n K q w) w‖≤Q*‖q‖:=by
    have leQ:Qn j≤Q:=Finset.single_le_sum (fun k _=>hQn k) (Finset.mem_range.mpr (by omega))
    calc
      _ ≤ ∑i∈Finset.range (j+1),(j.choose i:ℝ)*‖iteratedFDeriv ℝ i (fun w=>ψ (p,w)) w‖*
          ‖iteratedFDeriv ℝ (j-i) (SupportedJetFourierEvaluation.physical n K q) w‖:=
        norm_iteratedFDeriv_mul_le fs fq w (by exact_mod_cast hj)
      _ ≤ ∑i∈Finset.range (j+1),(j.choose i:ℝ)*B i*‖q‖:=by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul (mul_le_mul_of_nonneg_left (symbolBound i p hp w hw) (Nat.cast_nonneg _))
          (BoundedFiniteJetSpace.derivative_le n q.val (j-i) (by omega) w) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (hB i))
      _ = Qn j*‖q‖:=by rw [←Finset.sum_mul]
      _ ≤ _:=mul_le_mul_of_nonneg_right leQ (norm_nonneg _)
  have raw:=CompactFiniteFourierDecay.uniform_bound_of_derivatives compactK supported n
    (fs.mul fq) (Q*‖q‖) estimate z
  exact raw.trans_eq (by dsimp [C];ring)
end LeanShared.CompactSymbolMultiplierEnvelope
