module
public import LeanShared.Geometry.LocalFractionalJet
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Actual higher fractional jets are closed under addition. The derivative
identity is used only on the constructed neighborhood where both maps
have their genuine required differentiability. -/
public noncomputable section
namespace LeanShared.FractionalManifoldRegularity.JetAt
open Set Filter
open scoped Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem add {n : ℕ} {a : ℝ} {f g : E → F} {x : E}
    (hf : JetAt n a f x) (hg : JetAt n a g x) : JetAt n a (fun y => f y+g y) x := by
  obtain ⟨U,openU,inU,C,hC,boundF⟩ := hf.holder
  obtain ⟨V,openV,inV,D,hD,boundG⟩ := hg.holder
  obtain ⟨W,subW,openW,inW⟩ := mem_nhds_iff.mp (inter_mem
    (inter_mem (openU.mem_nhds inU) (openV.mem_nhds inV))
    (inter_mem (hf.smooth.eventually (by simp)) (hg.smooth.eventually (by simp))))
  refine ⟨hf.smooth.add hg.smooth,W,openW,inW,C+D,add_nonneg hC hD,?_⟩
  intro y hy z hz
  have sy := (subW hy).2
  have sz := (subW hz).2
  change ‖iteratedFDeriv ℝ n (f+g) y-iteratedFDeriv ℝ n (f+g) z‖ ≤ _
  rw [iteratedFDeriv_add_apply sy.1 sy.2,iteratedFDeriv_add_apply sz.1 sz.2]
  have split : (iteratedFDeriv ℝ n f y+iteratedFDeriv ℝ n g y)-
      (iteratedFDeriv ℝ n f z+iteratedFDeriv ℝ n g z) =
      (iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f z)+
      (iteratedFDeriv ℝ n g y-iteratedFDeriv ℝ n g z) := by abel
  rw [split]
  exact (norm_add_le _ _).trans ((add_le_add
    (boundF y (subW hy).1.1 z (subW hz).1.1)
    (boundG y (subW hy).1.2 z (subW hz).1.2)).trans_eq (by ring))

end LeanShared.FractionalManifoldRegularity.JetAt
