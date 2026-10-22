module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Postcomposition by an actual real linear isometry preserves the
literal C^r chart regularity at every real order, including higher jets. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F G M:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]

 theorem Regular.comp_linearIsometry {r:ℝ} {f:M→F} (hf:Regular (E:=E) (F:=F) r f)
    (L:F→ₗᵢ[ℝ]G) : Regular (E:=E) (F:=G) r (fun x=>L (f x)) := by
  refine ⟨hf.nonnegative,L.toContinuousLinearMap.contMDiff.comp hf.differentiable,?_⟩
  intro neq x
  obtain ⟨U,hU,hx,hsub,C,hC,bound⟩ := hf.holder neq x
  refine ⟨U,hU,hx,?_,C,hC,?_⟩
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
        L.toContinuousLinearMap ∘ chartMap (E:=E) (F:=F) f x := by
      simp only [chartMap,extChartAt_model_space_eq_id,PartialEquiv.refl_coe,
        Function.comp_def,id_eq,LinearIsometry.coe_toContinuousLinearMap]
    rw [chart,L.toContinuousLinearMap.iteratedFDeriv_comp_left (smooth y hy) le_rfl,
      L.toContinuousLinearMap.iteratedFDeriv_comp_left (smooth z hz) le_rfl]
    have difference : L.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) y)-
        L.toContinuousLinearMap.compContinuousMultilinearMap
        (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) z)=
        L.toContinuousLinearMap.compContinuousMultilinearMap
          (iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) y-
            iteratedFDeriv ℝ ⌊r⌋₊ (chartMap (E:=E) (F:=F) f x) z) := by
      ext v
      exact (map_sub L.toContinuousLinearMap _ _).symm
    rw [difference,L.norm_compContinuousMultilinearMap]
    exact bound y hy z hz
theorem Regular.ofReal {r:ℝ} {f:M→ℝ} (hf:Regular (E:=E) (F:=ℝ) r f) :
    Regular (E:=E) (F:=ℂ) r (fun x=>(f x:ℂ)) :=
  hf.comp_linearIsometry Complex.ofRealLI

end LeanShared.FractionalManifoldRegularity
