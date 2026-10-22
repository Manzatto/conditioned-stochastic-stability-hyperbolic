module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Analytic.Linear

/-! Continuous linear maps preserve Banach-valued meromorphic germs. -/

public section
namespace LeanShared.MeromorphicLinearMap
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Apply a continuous linear map to a meromorphic germ. -/
theorem map (L : E →L[𝕜] F) {f : 𝕜 → E} {z : 𝕜} (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => L (f w)) z := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have mapped : AnalyticAt 𝕜 (fun w => L ((w - z) ^ n • f w)) z :=
    (L.analyticAt _).comp hn
  simpa only [Function.comp_apply, map_smul] using mapped

end LeanShared.MeromorphicLinearMap
