module
public import LeanShared.Geometry.LocalFractionalJetFullComposition
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! The actual inverse of a C^r homeomorphism with invertible actual
differentials retains the full real order r, including its top two-point
Holder derivative. No extra ordinary derivative is requested. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff Manifold
namespace LeanShared.FractionalManifoldRegularity
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
theorem homeomorph_fderiv_inverse (H : E ≃ₜ F) (D : E → E ≃L[ℝ] F)
    (derivative : ∀ x, HasFDerivAt H (D x).toContinuousLinearMap x) (y : F) :
    fderiv ℝ H.symm y = ContinuousLinearMap.inverse (fderiv ℝ H (H.symm y)) := by
  rw [(derivative (H.symm y)).fderiv, ContinuousLinearMap.inverse_equiv]
  exact (H.toOpenPartialHomeomorph.hasFDerivAt_symm (mem_univ y) (derivative (H.symm y))).fderiv

set_option maxHeartbeats 3200000 in
theorem JetAt.homeomorph_inverse (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (H : E ≃ₜ F) (D : E → E ≃L[ℝ] F)
    (derivative : ∀ x, HasFDerivAt H (D x).toContinuousLinearMap x)
    (smooth1 : ContDiff ℝ 1 H) : ∀ x, JetAt n a H x → JetAt n a H.symm (H x) := by
  have inverseC1 : ContDiff ℝ 1 H.symm := H.contDiff_symm derivative smooth1
  induction n with
  | zero =>
    intro x _
    exact JetAt.of_contDiff_succ ha1 inverseC1.contDiffAt
  | succ n ih =>
    intro x hf
    have inverseJet := ih x (JetAt.of_contDiff_succ ha1 hf.smooth)
    have derivativeJet : JetAt n a (fderiv ℝ H) (H.symm (H x)) := by
      simpa only [H.symm_apply_apply] using hf.derivative
    have composed := JetAt.comp_of_c1_inner n ha ha1 derivativeJet inverseJet inverseC1.contDiffAt
    have operatorSmooth : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse
        ((fderiv ℝ H ∘ H.symm) (H x)) := by
      rw [Function.comp_apply, H.symm_apply_apply, (derivative x).fderiv]
      exact contDiffAt_map_inverse (D x)
    have inverseDerivativeJet := JetAt.smooth_comp n ha ha1 operatorSmooth composed
    have forwardSmooth : ContDiffAt ℝ (n+1 : ℕ) H (H.symm (H x)) := by
      simpa only [H.symm_apply_apply] using hf.smooth
    have inverseSmooth : ContDiffAt ℝ (n+1 : ℕ) H.symm (H x) :=
      H.toOpenPartialHomeomorph.contDiffAt_symm (mem_univ _) (derivative _) forwardSmooth
    apply JetAt.of_derivative inverseSmooth
    apply inverseDerivativeJet.congr
    exact Eventually.of_forall (fun y => (homeomorph_fderiv_inverse H D derivative y).symm)

/-- Full real-indexed regularity of the genuine inverse on model spaces. -/
theorem Regular.homeomorph_inverse {r : ℝ} (hr : 1 ≤ r) (H : E ≃ₜ F)
    (D : E → E ≃L[ℝ] F) (derivative : ∀ x, HasFDerivAt H (D x).toContinuousLinearMap x)
    (regular : Regular (E := E) (F := F) r H) :
    Regular (E := F) (F := E) r H.symm := by
  have forwardSmooth : ContDiff ℝ (⌊r⌋₊ : ℕ) H := regular.differentiable.contDiff
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr)
  have smooth1 : ContDiff ℝ 1 H := forwardSmooth.of_le (by exact_mod_cast order)
  refine ⟨regular.nonnegative, (H.contDiff_symm derivative forwardSmooth).contMDiff, ?_⟩
  intro unequal y
  let x := H.symm y
  have fraction_nonnegative : 0 ≤ r-(⌊r⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le regular.nonnegative)
  have fraction_le_one : r-(⌊r⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one r]
  obtain ⟨U, openU, inU, _domainU, C, hC, bound⟩ := regular.holder unequal x
  have forwardChart : chartMap (E := E) (F := F) H x = H := by simp [chartMap, chartAt_self_eq]
  have forwardJet : JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) H x := by
    refine ⟨forwardSmooth.contDiffAt, U, openU, ?_, C, hC, ?_⟩
    · simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using inU
    · simpa only [forwardChart] using bound
  have inverseJet := JetAt.homeomorph_inverse ⌊r⌋₊ fraction_nonnegative fraction_le_one
    H D derivative smooth1 x forwardJet
  have here : H x = y := H.apply_symm_apply y
  rw [here] at inverseJet
  obtain ⟨W, openW, inW, A, hA, boundW⟩ := inverseJet.holder
  refine ⟨W, openW, ?_, ?_, A, hA, ?_⟩
  · simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using inW
  · simp only [chartDomain, extChartAt_model_space_eq_id, PartialEquiv.refl_source,
      Set.preimage_univ, Set.inter_univ]
    exact subset_univ W
  · have inverseChart : chartMap (E := F) (F := E) H.symm y = H.symm := by
      simp [chartMap, chartAt_self_eq]
    simpa only [inverseChart] using boundW

end LeanShared.FractionalManifoldRegularity
