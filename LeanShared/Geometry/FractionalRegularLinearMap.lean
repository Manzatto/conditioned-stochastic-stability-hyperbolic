module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Ring

/-! Postcomposition by an actual bounded real linear map preserves the
literal C^r chart regularity at every real order, including higher jets. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F G M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

 theorem Regular.comp_continuousLinearMap {r:ℝ} {f:M→F} (hf:Regular (E:=E) (F:=F) r f)
    (L:F→L[ℝ]G) : Regular (E:=E) (F:=G) r (fun x=>L (f x)) := by
  refine ⟨hf.nonnegative,L.contMDiff.comp hf.differentiable,?_⟩
  intro neq x
  obtain ⟨U,hU,hx,hsub,C,hC,bound⟩ := hf.holder neq x
  refine ⟨U,hU,hx,?_,‖L‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  · intro y hy
    refine ⟨(hsub hy).1,?_⟩
    simp only [Set.mem_preimage,extChartAt_model_space_eq_id,PartialEquiv.refl_source,mem_univ]
  · intro y hy z hz
    let e := extChartAt (𝓘(ℝ,E)) x
    have smooth (v:E) (hv:v∈U) : ContDiffAt ℝ (⌊r⌋₊:ℕ) (chartMap (E:=E) (F:=F) f x) v := by
      have inv : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) (⌊r⌋₊:ℕ) e.symm v :=
        (contMDiffOn_extChartAt_symm (I:=𝓘(ℝ,E)) (n:=(⌊r⌋₊:ℕ)) x).contMDiffAt
          ((isOpen_extChartAt_target x).mem_nhds (hsub hv).1)
      simpa only [chartMap,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
        Function.comp_def,id_eq] using (hf.differentiable.contMDiffAt.comp v inv).contDiffAt
    have chart : chartMap (E:=E) (F:=G) (fun x=>L (f x)) x=
        L ∘ chartMap (E:=E) (F:=F) f x := by
      simp only [chartMap,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
        Function.comp_def,id_eq]
    rw [chart,L.iteratedFDeriv_comp_left (smooth y hy) le_rfl,
      L.iteratedFDeriv_comp_left (smooth z hz) le_rfl]
    have difference : L.compContinuousMultilinearMap
        (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) y)-
        L.compContinuousMultilinearMap
        (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) z)=
        L.compContinuousMultilinearMap
          (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) y-
            iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) z) := by
      ext v
      exact (map_sub L _ _).symm
    rw [difference]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      ((mul_le_mul_of_nonneg_left (bound y hy z hz) (norm_nonneg L)).trans_eq (by ring))

end LeanShared.FractionalManifoldRegularity
