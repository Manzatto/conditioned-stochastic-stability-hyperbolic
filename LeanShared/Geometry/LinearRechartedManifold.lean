module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Changing a boundaryless manifold's coordinate model through an actual
continuous linear equivalence. In particular, max-norm Cartesian charts
can be replaced by the genuine Hilbert `WithLp 2` model. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.LinearRechartedManifold

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The new coordinate chart is literally the old chart followed by the
specified linear equivalence. -/
@[instance_reducible] def charts (e : E ≃L[ℝ] F) : ChartedSpace F M where
  atlas := (fun c : OpenPartialHomeomorph M E => c.trans e.toHomeomorph.toOpenPartialHomeomorph) ''
    atlas E M
  chartAt x := (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by simp
  chart_mem_atlas x := ⟨chartAt E x, chart_mem_atlas E x, rfl⟩

theorem chartAt_eq (e : E ≃L[ℝ] F) (x : M) :
    (letI := charts (M := M) e; chartAt F x) =
      (chartAt E x).trans e.toHomeomorph.toOpenPartialHomeomorph := rfl

/-- Smoothness is preserved by the constructed change of linear model. -/
theorem manifold (e : E ≃L[ℝ] F) [IsManifold (𝓘(ℝ, E)) ∞ M] :
    letI := charts (M := M) e; IsManifold (𝓘(ℝ, F)) ∞ M := by
  let := charts (M := M) e
  apply isManifold_of_contDiffOn (𝓘(ℝ, F)) ∞ M
  rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
  have hb := ((contDiffGroupoid ∞ (𝓘(ℝ, E))).compatible hc hd).1
  have hb' : ContDiffOn ℝ ∞ (c.symm.trans d) (c.symm.trans d).source := by
    simpa only [contDiffPregroupoid, mfld_simps] using hb
  have hs : MapsTo e.symm
      (((c.trans e.toHomeomorph.toOpenPartialHomeomorph).symm.trans
        (d.trans e.toHomeomorph.toOpenPartialHomeomorph)).source)
      (c.symm.trans d).source := by
    intro v hv
    simpa only [mfld_simps, ContinuousLinearEquiv.coe_symm_toHomeomorph] using hv
  have hh := e.contDiff.comp_contDiffOn (hb'.comp e.symm.contDiff.contDiffOn hs)
  simpa only [mfld_simps, Function.comp_def, ContinuousLinearEquiv.coe_toHomeomorph,
    ContinuousLinearEquiv.coe_symm_toHomeomorph] using hh

/-- Actual Hilbert product coordinates, topologically equivalent to the
ordinary max-norm Cartesian coordinates. -/
def hilbertProductEquiv {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] :
    (A × B) ≃L[ℝ] WithLp 2 (A × B) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm

section HilbertProduct
variable {A B X Y : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [TopologicalSpace X] [ChartedSpace A X]
  [TopologicalSpace Y] [ChartedSpace B Y]

/-- Actual product charts in the Hilbert direct sum model. The norm is the
library ℓ² norm, and no incompatible inner product is placed on a max norm. -/
@[instance_reducible] def productCharts : ChartedSpace (WithLp 2 (A × B)) (X × Y) := by
  letI : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  exact charts (M := X × Y) (hilbertProductEquiv (A := A) (B := B))

theorem product_chart_apply (x z : X × Y) :
    (letI := productCharts (A := A) (B := B) (X := X) (Y := Y);
      chartAt (WithLp 2 (A × B)) x) z =
      WithLp.toLp 2 ((chartAt A x.1) z.1, (chartAt B x.2) z.2) := rfl

theorem product_chart_symm_apply (x : X × Y) (v : WithLp 2 (A × B)) :
    (letI := productCharts (A := A) (B := B) (X := X) (Y := Y);
      (chartAt (WithLp 2 (A × B)) x).symm) v =
      ((chartAt A x.1).symm v.fst, (chartAt B x.2).symm v.snd) := rfl

/-- The constructed product is a genuine smooth manifold with Hilbert
coordinate model, suitable for the Fourier/anisotropic construction. -/
theorem product_manifold [IsManifold (𝓘(ℝ, A)) ∞ X] [IsManifold (𝓘(ℝ, B)) ∞ Y] :
    letI := productCharts (A := A) (B := B) (X := X) (Y := Y);
      IsManifold (𝓘(ℝ, WithLp 2 (A × B))) ∞ (X × Y) := by
  let : ChartedSpace (A × B) (X × Y) := prodChartedSpace A X B Y
  let : IsManifold (𝓘(ℝ, A × B)) ∞ (X × Y) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓘(ℝ, A)) (I' := 𝓘(ℝ, B)) X Y
  exact manifold (M := X × Y) (hilbertProductEquiv (A := A) (B := B))

end HilbertProduct

end LeanShared.LinearRechartedManifold
