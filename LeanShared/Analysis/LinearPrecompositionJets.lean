module
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! All-order jet transport under a linear map on the source. The derivative
formula needs only the actual local C^k regularity at the source image. -/
public noncomputable section
open Set Function Filter
open scoped Topology
namespace LeanShared.LinearPrecompositionJets
variable {E F G:Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

@[expose] def transport (L:G→L[ℝ]E) (k:ℕ) :
    ContinuousMultilinearMap ℝ (fun _:Fin k=>E) F →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _:Fin k=>G) F where
  toFun A := A.compContinuousLinearMap (fun _=>L)
  map_add' A B := by ext v; simp
  map_smul' c A := by ext v; simp

theorem norm_transport_le (L:G→L[ℝ]E) (k:ℕ)
    (A:ContinuousMultilinearMap ℝ (fun _:Fin k=>E) F) :
    ‖transport L k A‖≤‖L‖^k*‖A‖ := by
  change ‖A.compContinuousLinearMap (fun _ : Fin k=>L)‖≤‖L‖^k*‖A‖
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_comm] using
    A.norm_compContinuousLinearMap_le (fun _:Fin k=>L)

theorem iteratedFDeriv_comp_right_at (L:G→L[ℝ]E) {f:E→F} (k:ℕ) (x:G)
    (regular:ContDiffAt ℝ (k:ℕ) f (L x)) :
    iteratedFDeriv ℝ k (f ∘ L) x=transport L k (iteratedFDeriv ℝ k f (L x)) := by
  obtain ⟨U,nearU,smoothU⟩ := regular.contDiffOn le_rfl (by simp)
  obtain ⟨V,inside,openV,inV⟩ := mem_nhds_iff.mp nearU
  have openPre : IsOpen (L ⁻¹' V) := openV.preimage L.continuous
  have formula := L.iteratedFDerivWithin_comp_right (smoothU.mono inside)
    openV.uniqueDiffOn openPre.uniqueDiffOn inV le_rfl
  rw [iteratedFDerivWithin_of_isOpen k openPre (show x∈L ⁻¹' V from inV),
    iteratedFDerivWithin_of_isOpen k openV inV] at formula
  exact formula

end LeanShared.LinearPrecompositionJets
