module
public import LeanShared.Geometry.LocalFractionalJet
public import LeanShared.Analysis.LinearPrecompositionJets
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! Arbitrary-order local Holder jets pull back along every continuous
linear source map, with an explicit operator-norm constant. -/
public noncomputable section
open Set Filter Function
open scoped Topology ContDiff
namespace LeanShared.FractionalManifoldRegularity.JetAt
variable {E F G:Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem comp_linear {n:ℕ} {a:ℝ} (ha:0≤a) (L:G→L[ℝ]E) {f:E→F} {x:G}
    (hf:JetAt n a f (L x)) : JetAt n a (f ∘ L) x := by
  obtain ⟨U,nearU,smoothU⟩ := hf.smooth.contDiffOn le_rfl (by simp)
  obtain ⟨V,inside,openV,inV⟩ := mem_nhds_iff.mp nearU
  obtain ⟨W,openW,inW,C,nonnegative,bound⟩ := hf.holder
  let O := L ⁻¹' (V∩W)
  have openO : IsOpen O := (openV.inter openW).preimage L.continuous
  refine ⟨hf.smooth.comp x L.contDiff.contDiffAt,O,openO,⟨inV,inW⟩,
    (‖L‖^n*C)*‖L‖^a,by positivity,?_⟩
  intro y hy z hz
  have smoothY := (smoothU.mono inside) (L y) hy.1
  have smoothZ := (smoothU.mono inside) (L z) hz.1
  rw [LinearPrecompositionJets.iteratedFDeriv_comp_right_at L n y
      (smoothY.contDiffAt (openV.mem_nhds hy.1)),
    LinearPrecompositionJets.iteratedFDeriv_comp_right_at L n z
      (smoothZ.contDiffAt (openV.mem_nhds hz.1)),←map_sub]
  calc
    _ ≤ ‖L‖^n*‖iteratedFDeriv ℝ n f (L y)-iteratedFDeriv ℝ n f (L z)‖ :=
      LinearPrecompositionJets.norm_transport_le L n _
    _ ≤ ‖L‖^n*(C*‖L y-L z‖^a) :=
      mul_le_mul_of_nonneg_left (bound (L y) hy.2 (L z) hz.2) (pow_nonneg (norm_nonneg _) n)
    _ ≤ ‖L‖^n*(C*(‖L‖*‖y-z‖)^a) := by
      gcongr
      simpa only [map_sub] using L.le_opNorm (y-z)
    _ = (‖L‖^n*C)*‖L‖^a*‖y-z‖^a := by
      rw [Real.mul_rpow (norm_nonneg L) (norm_nonneg (y-z))]
      ring

end LeanShared.FractionalManifoldRegularity.JetAt
