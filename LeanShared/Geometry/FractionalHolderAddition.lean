module
public import LeanShared.Geometry.FractionalManifoldRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Closure under addition in the actual fractional manifold class of
order between zero and one. This supports finite chart-patch sums without
supplying a fractional-calculus source for the reconstructed function. -/
public noncomputable section
open Set
open scoped Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

theorem add_of_order_lt_one {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    {f g : M → F} (hf : Regular (E := E) (F := F) a f)
    (hg : Regular (E := E) (F := F) a g) :
    Regular (E := E) (F := F) a (fun x => f x + g x) := by
  have floor : ⌊a⌋₊ = 0 := Nat.floor_eq_zero.mpr ha1
  have unequal : a ≠ (⌊a⌋₊ : ℝ) := by simpa only [floor, Nat.cast_zero] using ha.ne'
  refine ⟨ha.le, ?_, ?_⟩
  · rw [floor]
    exact contMDiff_zero_iff.mpr (hf.differentiable.continuous.add hg.differentiable.continuous)
  · intro _ x
    obtain ⟨U, hU, inU, subU, C, hC, boundF⟩ := hf.holder unequal x
    obtain ⟨W, hW, inW, _, D, hD, boundG⟩ := hg.holder unequal x
    refine ⟨U ∩ W, hU.inter hW, ⟨inU, inW⟩, ?_, C + D, add_nonneg hC hD, ?_⟩
    · have domains : chartDomain (E := E) (F := F) f x =
          chartDomain (E := E) (F := F) (fun z => f z + g z) x := by
        simp only [chartDomain, extChartAt_model_space_eq_id, PartialEquiv.refl_source,
          preimage_univ, inter_univ]
      rw [← domains]
      exact inter_subset_left.trans subU
    · intro y hy z hz
      have fbound := boundF y hy.1 z hz.1
      have gbound := boundG y hy.2 z hz.2
      rw [floor] at fbound gbound ⊢
      simp only [Nat.cast_zero, sub_zero, iteratedFDeriv_zero_eq_comp,
        Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map,
        chartMap, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] at fbound gbound ⊢
      have algebra : (f ((extChartAt (𝓘(ℝ,E)) x).symm y) + g ((extChartAt (𝓘(ℝ,E)) x).symm y)) -
          (f ((extChartAt (𝓘(ℝ,E)) x).symm z) + g ((extChartAt (𝓘(ℝ,E)) x).symm z)) =
          (f ((extChartAt (𝓘(ℝ,E)) x).symm y) - f ((extChartAt (𝓘(ℝ,E)) x).symm z)) +
          (g ((extChartAt (𝓘(ℝ,E)) x).symm y) - g ((extChartAt (𝓘(ℝ,E)) x).symm z)) := by abel
      rw [algebra]
      exact (norm_add_le _ _).trans (by nlinarith only [fbound, gbound])
end LeanShared.FractionalManifoldRegularity
