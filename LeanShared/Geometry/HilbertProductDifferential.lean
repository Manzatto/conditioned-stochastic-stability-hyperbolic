module

public import LeanShared.Geometry.LinearRechartedIdentity
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! Actual Hilbert product projections are smooth. Their genuine manifold
derivatives intertwine the literal product map with each factor derivative. -/
public noncomputable section
open IsManifold
open scoped Manifold ContDiff
namespace LeanShared.HilbertProductDifferential
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace F Y]
local instance oldCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance newCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts

theorem smooth_fst : ContMDiff (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,E)) ∞ (@Prod.fst X Y) := by
  have back := LinearRechartedManifold.identity_backward (M := X × Y)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F))
  have first : ContMDiff (𝓘(ℝ,E × F)) (𝓘(ℝ,E)) ∞ (@Prod.fst X Y) := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_fst : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,F))) (𝓘(ℝ,E)) ∞ (@Prod.fst X Y))
  exact first.comp back

theorem smooth_snd : ContMDiff (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,F)) ∞ (@Prod.snd X Y) := by
  have back := LinearRechartedManifold.identity_backward (M := X × Y)
    (LinearRechartedManifold.hilbertProductEquiv (A := E) (B := F))
  have second : ContMDiff (𝓘(ℝ,E × F)) (𝓘(ℝ,F)) ∞ (@Prod.snd X Y) := by
    simpa only [modelWithCornersSelf_prod] using
      (contMDiff_snd : ContMDiff ((𝓘(ℝ,E)).prod (𝓘(ℝ,F))) (𝓘(ℝ,F)) ∞ (@Prod.snd X Y))
  exact second.comp back

theorem fst_intertwines (T : X → X) (S : Y → Y)
    (forward : MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (product : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) (Prod.map T S))
    (z : X × Y) :
    (mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,E)) Prod.fst (Prod.map T S z)).comp
      (mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) (Prod.map T S) z) =
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) T z.1).comp
      (mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,E)) Prod.fst z) := by
  have projection := (smooth_fst (E := E) (F := F) (X := X) (Y := Y)).mdifferentiable (by simp)
  have left := mfderiv_comp z (projection (Prod.map T S z)) (product z)
  have right := mfderiv_comp z (forward z.1) (projection z)
  exact left.symm.trans right

theorem snd_intertwines (T : X → X) (S : Y → Y)
    (forward : MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (product : MDifferentiable (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) (Prod.map T S))
    (z : X × Y) :
    (mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,F)) Prod.snd (Prod.map T S z)).comp
      (mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,WithLp 2 (E × F))) (Prod.map T S) z) =
    (mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) S z.2).comp
      (mfderiv (𝓘(ℝ,WithLp 2 (E × F))) (𝓘(ℝ,F)) Prod.snd z) := by
  have projection := (smooth_snd (E := E) (F := F) (X := X) (Y := Y)).mdifferentiable (by simp)
  have left := mfderiv_comp z (projection (Prod.map T S z)) (product z)
  have right := mfderiv_comp z (forward z.2) (projection z)
  exact left.symm.trans right

end LeanShared.HilbertProductDifferential
