module
public import LeanShared.MeasureTheory.OrthogonalFubini
public import LeanShared.Analysis.LeafwiseFubiniPairing

/-! A bound on actual parallel Euclidean leaves controls ambient test
pairings. Both the change of variables and product normalization are proved. -/
public section
open MeasureTheory
namespace LeanShared.OrthogonalLeafPairing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem bound (P : Submodule ℝ E) (f test : E → ℂ) (A C : ℝ) (hC : 0 ≤ C)
    (w : Pᗮ → ℝ) (nonnegative : ∀ v, 0 ≤ w v) (integrableW : Integrable w)
    (integrableProduct : Integrable (fun x => f x*test x))
    (integrableLeaves : ∀ v : Pᗮ, Integrable (fun u : P => f ((u:E)+(v:E))))
    (leafBound : ∀ v : Pᗮ, (∫ u : P, ‖f ((u:E)+(v:E))‖) ≤ A)
    (testBound : ∀ (u : P) (v : Pᗮ), ‖test ((u:E)+(v:E))‖ ≤ C*w v) :
    ‖∫ x, f x*test x‖ ≤ (C*A)*(∫ v, w v) := by
  have changeVariables := (OrthogonalFubini.preserving P).integral_comp' (fun x => f x*test x)
  have productIntegrable : Integrable
      (fun z : P × Pᗮ => f (OrthogonalFubini.split P z)*test (OrthogonalFubini.split P z)) :=
    (OrthogonalFubini.preserving P).integrable_comp_emb
      (OrthogonalFubini.split P).measurableEmbedding |>.mpr integrableProduct
  rw [← changeVariables]
  simp only [OrthogonalFubini.split_apply] at productIntegrable ⊢
  exact LeafwiseFubiniPairing.bound volume volume
    (fun z : P × Pᗮ => f ((z.1:E)+(z.2:E)))
    (fun z : P × Pᗮ => test ((z.1:E)+(z.2:E))) A C hC w nonnegative integrableW
    productIntegrable integrableLeaves leafBound testBound
end LeanShared.OrthogonalLeafPairing
