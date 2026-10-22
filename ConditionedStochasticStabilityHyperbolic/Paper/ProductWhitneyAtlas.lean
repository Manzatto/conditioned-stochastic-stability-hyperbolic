module

public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-! The finite Whitney atlas of a Cartesian product is constructed from the
actual factor charts and patches. No global coordinate trivialization is
introduced. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise

variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y]
  {T : X → X} {T' : Y → Y}

/-- Canonical product charts, with the model type tag removed only locally.
The dictionary is explicit in the constructed atlas and adds no geometry. -/
local instance productCharts : ChartedSpace (E × F) (X × Y) :=
  prodChartedSpace E X F Y

def WhitneyAtlas.product (A : WhitneyAtlas (E := E) T) (B : WhitneyAtlas (E := F) T') :
    WhitneyAtlas (E := E × F) (Prod.map T T') where
  count := A.count * B.count
  source i := (A.source (finProdFinEquiv.symm i).1).prod (B.source (finProdFinEquiv.symm i).2)
  target i := (A.target (finProdFinEquiv.symm i).1).prod (B.target (finProdFinEquiv.symm i).2)
  source_smooth i := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (A.source_smooth _) (B.source_smooth _)
  target_smooth i := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.mem_maximalAtlas_prod (A.target_smooth _) (B.target_smooth _)
  patch i := A.patch (finProdFinEquiv.symm i).1 ×ˢ B.patch (finProdFinEquiv.symm i).2
  patch_open i := (A.patch_open _).prod (B.patch_open _)
  patch_cover := by
    apply eq_univ_of_forall
    intro z
    have hx : z.1 ∈ ⋃ i, A.patch i := A.patch_cover.symm ▸ mem_univ z.1
    have hy : z.2 ∈ ⋃ i, B.patch i := B.patch_cover.symm ▸ mem_univ z.2
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    apply mem_iUnion.mpr
    exact ⟨finProdFinEquiv (i, j), by simpa only [Equiv.symm_apply_apply, Set.mem_prod] using And.intro hi hj⟩
  patch_compact i := by
    rw [closure_prod_eq]
    exact (A.patch_compact _).prod (B.patch_compact _)
  patch_source i := by
    rw [closure_prod_eq]
    exact Set.prod_mono (A.patch_source _) (B.patch_source _)
  deterministic_target i := by
    rintro _ ⟨z, hz, rfl⟩
    rw [closure_prod_eq] at hz
    exact ⟨A.deterministic_target _ ⟨z.1, hz.1, rfl⟩,
      B.deterministic_target _ ⟨z.2, hz.2, rfl⟩⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
