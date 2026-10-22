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
local instance smoothMapOldCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance smoothMapNewCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts

theorem contMDiff_map {n:ℕ} (T:X→X) (S:Y→Y)
    (first:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) n T)
    (second:ContMDiff (𝓘(ℝ,F)) (𝓘(ℝ,F)) n S) :
    ContMDiff (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) n (Prod.map T S) := by
  have ordinary : ContMDiff (𝓘(ℝ,E×F)) (𝓘(ℝ,E×F)) n (Prod.map T S) := by
    simpa only [modelWithCornersSelf_prod] using first.prodMap second
  have front := (LinearRechartedManifold.identity_forward (M:=X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F))).of_le (show (n:WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  have back := (LinearRechartedManifold.identity_backward (M:=X×Y)
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F))).of_le (show (n:WithTop ℕ∞) ≤ ∞ by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  exact front.comp (ordinary.comp back)

end LeanShared.HilbertProductDifferential
