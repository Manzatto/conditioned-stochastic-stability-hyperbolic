module
public import LeanShared.Geometry.LocalFractionalJet

/-! Linear postcomposition of local fractional jets, allowing independent
universes for the original and normalized coordinate models. -/
public noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace LeanShared.FractionalManifoldRegularity.JetAt
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem linear_comp {n : ℕ} {a : ℝ} (L : F →L[ℝ] G) {f : E → F} {x : E}
    (hf : JetAt n a f x) : JetAt n a (L ∘ f) x := by
  obtain ⟨U, nearU, smoothU⟩ := hf.smooth.contDiffOn le_rfl (by simp)
  obtain ⟨V, inside, openV, inV⟩ := mem_nhds_iff.mp nearU
  obtain ⟨W, openW, inW, C, nonnegative, bound⟩ := hf.holder
  refine ⟨L.contDiff.contDiffAt.comp x hf.smooth, V∩W, openV.inter openW,
    ⟨inV, inW⟩, ‖L‖*C, mul_nonneg (norm_nonneg _) nonnegative, ?_⟩
  intro y hy z hz
  have smoothY := ((smoothU.mono inside) y hy.1).contDiffAt (openV.mem_nhds hy.1)
  have smoothZ := ((smoothU.mono inside) z hz.1).contDiffAt (openV.mem_nhds hz.1)
  rw [L.iteratedFDeriv_comp_left smoothY le_rfl, L.iteratedFDeriv_comp_left smoothZ le_rfl]
  have difference :
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f y)-
          L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f z) =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f z) := by
    ext v
    simp
  rw [difference]
  calc
    _ ≤ ‖L‖*‖iteratedFDeriv ℝ n f y-iteratedFDeriv ℝ n f z‖ :=
      L.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖L‖*(C*‖y-z‖^a) :=
      mul_le_mul_of_nonneg_left (bound y hy.2 z hz.2) (norm_nonneg _)
    _ = (‖L‖*C)*‖y-z‖^a := (mul_assoc _ _ _).symm

end LeanShared.FractionalManifoldRegularity.JetAt
