module
public import LeanShared.Geometry.LocalFractionalJetLinear
public import LeanShared.Geometry.FractionalManifoldRegularity
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Actual arbitrary-order fractional regularity of Cartesian product
maps, derived from two-point top-jet estimates in the literal charts. -/
@[expose] public noncomputable section
open Set Filter Function IsManifold
open scoped Topology ContDiff Manifold
namespace LeanShared.FractionalManifoldRegularity.JetAt
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Local two-point top jets pair in the actual maximum product norm. -/
theorem prodMk {n : ℕ} {a : ℝ} {f : E → F} {g : E → G} {x : E}
    (hf : JetAt n a f x) (hg : JetAt n a g x) : JetAt n a (fun y => (f y, g y)) x := by
  obtain ⟨U, openU, inU, C, positiveC, boundF⟩ := hf.holder
  obtain ⟨V, openV, inV, D, positiveD, boundG⟩ := hg.holder
  obtain ⟨O, insideO, openO, inO⟩ := mem_nhds_iff.mp
    ((hf.smooth.eventually (by simp)).and (hg.smooth.eventually (by simp)))
  refine ⟨hf.smooth.prodMk hg.smooth, (U ∩ V) ∩ O,
    (openU.inter openV).inter openO, ⟨⟨inU, inV⟩, inO⟩,
    C + D, add_nonneg positiveC positiveD, ?_⟩
  intro y hy z hz
  rw [iteratedFDeriv_prodMk (insideO hy.2).1 (insideO hy.2).2 le_rfl,
    iteratedFDeriv_prodMk (insideO hz.2).1 (insideO hz.2).2 le_rfl,
    ← ContinuousMultilinearMap.sub_prod_sub, ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact (boundF y hy.1.1 z hz.1.1).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right positiveD) (Real.rpow_nonneg (norm_nonneg _) _))
  · exact (boundG y hy.1.2 z hz.1.2).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left positiveC) (Real.rpow_nonneg (norm_nonneg _) _))

end LeanShared.FractionalManifoldRegularity.JetAt

namespace LeanShared.FractionalManifoldRegularity
variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [ChartedSpace E X] [TopologicalSpace Y] [ChartedSpace F Y]

local instance cartesianCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y

theorem chartMap_prodMap (f : X → X) (g : Y → Y) (z : X × Y) :
    chartMap (E := E × F) (F := E × F) (Prod.map f g) z =
      fun y : E × F => (chartMap (E := E) (F := E) f z.1 y.1,
        chartMap (E := F) (F := F) g z.2 y.2) := by
  simp only [chartMap, extChartAt, mfld_simps, Function.comp_def]
  rfl

theorem chartDomain_prodMap (f : X → X) (g : Y → Y) (z : X × Y) :
    chartDomain (E := E × F) (F := E × F) (Prod.map f g) z =
      chartDomain (E := E) (F := E) f z.1 ×ˢ chartDomain (E := F) (F := F) g z.2 := by
  ext y
  simp only [chartDomain, extChartAt, mfld_simps]
  constructor
  · rintro ⟨⟨hy, hz⟩, hf, hg⟩
    exact ⟨⟨hy, hf⟩, hz, hg⟩
  · rintro ⟨⟨hy, hf⟩, hz, hg⟩
    exact ⟨⟨hy, hz⟩, hf, hg⟩

/-- Full actual real-order product regularity, with no fractional calculus
certificate and no rounding up of the differentiability order. -/
theorem Regular.prod_map {r : ℝ} {f : X → X} {g : Y → Y}
    (hf : Regular (E := E) (F := E) r f) (hg : Regular (E := F) (F := F) r g) :
    Regular (E := E × F) (F := E × F) r (Prod.map f g) := by
  refine ⟨hf.nonnegative, ?_, ?_⟩
  · rw [modelWithCornersSelf_prod]
    exact hf.differentiable.prodMap hg.differentiable
  · intro unequal z
    obtain ⟨U, openU, inU, insideU, C, positiveC, boundF⟩ := hf.holder unequal z.1
    obtain ⟨V, openV, inV, insideV, D, positiveD, boundG⟩ := hg.holder unequal z.2
    have smoothF : ContDiffAt ℝ (⌊r⌋₊ : ℕ)
        (chartMap (E := E) (F := E) f z.1) (extChartAt (𝓘(ℝ, E)) z.1 z.1) := by
      simpa only [chartMap, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using
        (contMDiffAt_iff.mp (hf.differentiable.contMDiffAt (x := z.1))).2
    have smoothG : ContDiffAt ℝ (⌊r⌋₊ : ℕ)
        (chartMap (E := F) (F := F) g z.2) (extChartAt (𝓘(ℝ, F)) z.2 z.2) := by
      simpa only [chartMap, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using
        (contMDiffAt_iff.mp (hg.differentiable.contMDiffAt (x := z.2))).2
    let center := (extChartAt (𝓘(ℝ, E)) z.1 z.1, extChartAt (𝓘(ℝ, F)) z.2 z.2)
    have first : JetAt ⌊r⌋₊ (r - (⌊r⌋₊ : ℝ))
        (chartMap (E := E) (F := E) f z.1) center.1 :=
      ⟨smoothF, U, openU, inU, C, positiveC, boundF⟩
    have second : JetAt ⌊r⌋₊ (r - (⌊r⌋₊ : ℝ))
        (chartMap (E := F) (F := F) g z.2) center.2 :=
      ⟨smoothG, V, openV, inV, D, positiveD, boundG⟩
    have exponent := sub_nonneg.mpr (Nat.floor_le hf.nonnegative)
    have left := first.comp_linear (x := center) exponent (ContinuousLinearMap.fst ℝ E F)
    have right := second.comp_linear (x := center) exponent (ContinuousLinearMap.snd ℝ E F)
    have paired := left.prodMk right
    obtain ⟨O, openO, inO, B, positiveB, bound⟩ := paired.holder
    refine ⟨O ∩ (U ×ˢ V), openO.inter (openU.prod openV), ?_, ?_, B, positiveB, ?_⟩
    · change center ∈ O ∩ (U ×ˢ V)
      exact ⟨inO, inU, inV⟩
    · intro y hy
      rw [chartDomain_prodMap]
      exact ⟨insideU hy.2.1, insideV hy.2.2⟩
    · intro y hy w hw
      rw [chartMap_prodMap]
      exact bound y hy.1 w hw.1

end LeanShared.FractionalManifoldRegularity
