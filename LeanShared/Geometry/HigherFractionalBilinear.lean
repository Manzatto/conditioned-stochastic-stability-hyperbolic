module
public import LeanShared.Geometry.FractionalJetCharacterization
public import LeanShared.Geometry.LocalFractionalJetBilinear
public import LeanShared.Geometry.SmoothFractionalRegularity

/-! Actual all-order fractional multiplication from the local derivative
product rule. No fractional product estimate is supplied as background. -/
public noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
universe u
variable {E F G H : Type u} {M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [TopologicalSpace M] [ChartedSpace E M]

theorem Regular.bilinear_noninteger {a : ℝ} {n : ℕ}
    (ha : 0 < a) (ha1 : a < 1) {f : M → F} {g : M → G}
    (hf : Regular (E := E) (F := F) (a+n) f)
    (hg : Regular (E := E) (F := G) (a+n) g) (B : F →L[ℝ] G →L[ℝ] H) :
    Regular (E := E) (F := H) (a+n) (fun x => B (f x) (g x)) := by
  apply regular_of_chart_jets ha ha1
  intro x
  have result := JetAt.bilinear n ha.le ha1.le B (hf.chart_jet ha ha1 x) (hg.chart_jet ha ha1 x)
  simpa only [chartMap, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.comp_def, id_eq] using result

end LeanShared.FractionalManifoldRegularity
