module
public import LeanShared.Geometry.LocalFractionalJetLinear
public import LeanShared.Geometry.HilbertProductDifferential
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Real-order regularity is preserved by the actual first projection of
the Hilbert-recharted product manifold. This applies to arbitrary vector
valued observables and supplies the scalar auxiliary-weight-one case. -/
public noncomputable section
open Set Function IsManifold
open scoped Manifold ContDiff Topology
namespace LeanShared.FractionalManifoldRegularity
variable {E F G X Y:Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [TopologicalSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
local instance firstOrdinaryCharts : ChartedSpace (E×F) (X×Y) := prodChartedSpace E X F Y
local instance firstHilbertCharts : ChartedSpace (WithLp 2 (E×F)) (X×Y) :=
  LinearRechartedManifold.productCharts
local instance firstHilbertManifold : IsManifold (𝓘(ℝ,WithLp 2 (E×F))) ∞ (X×Y) :=
  LinearRechartedManifold.product_manifold

@[expose] def firstCoordinateMap : WithLp 2 (E×F) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E F).comp
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F)).symm.toContinuousLinearMap

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
theorem first_coordinate_center (z:X×Y) :
    firstCoordinateMap (extChartAt (𝓘(ℝ,WithLp 2 (E×F))) z z)=
      extChartAt (𝓘(ℝ,E)) z.1 z.1 := by
  simp only [firstCoordinateMap,extChartAt,mfld_simps]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
theorem first_chartMap (f:X→G) (z:X×Y) :
    chartMap (E:=WithLp 2 (E×F)) (F:=G) (fun p:X×Y=>f p.1) z =
      chartMap (E:=E) (F:=G) f z.1 ∘ firstCoordinateMap (E:=E) (F:=F) := by
  simp only [chartMap,firstCoordinateMap,extChartAt,mfld_simps,Function.comp_def]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
/-- No product regularity or Holder bound is assumed. -/
theorem Regular.hilbert_fst {r:ℝ} {f:X→G} (hf:Regular (E:=E) (F:=G) r f) :
    Regular (E:=WithLp 2 (E×F)) (F:=G) r (fun z:X×Y=>f z.1) := by
  refine ⟨hf.nonnegative,hf.differentiable.comp
    ((HilbertProductDifferential.smooth_fst (E:=E) (F:=F) (X:=X) (Y:=Y)).of_le (by simp)),?_⟩
  intro unequal z
  have smooth : ContDiffAt ℝ (⌊r⌋₊:ℕ) (chartMap (E:=E) (F:=G) f z.1)
      (extChartAt (𝓘(ℝ,E)) z.1 z.1) := by
    simpa only [chartMap,ModelWithCorners.range_eq_univ,contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp (hf.differentiable.contMDiffAt (x:=z.1))).2
  obtain ⟨U,openU,inU,_inside,C,hC,bound⟩ := hf.holder unequal z.1
  have jet : JetAt ⌊r⌋₊ (r-(⌊r⌋₊:ℝ)) (chartMap (E:=E) (F:=G) f z.1)
      (firstCoordinateMap (E:=E) (F:=F) (extChartAt (𝓘(ℝ,WithLp 2 (E×F))) z z)) := by
    rw [first_coordinate_center]
    exact ⟨smooth,U,openU,inU,C,hC,bound⟩
  have made := jet.comp_linear (sub_nonneg.mpr (Nat.floor_le hf.nonnegative))
    (firstCoordinateMap (E:=E) (F:=F))
  rw [←first_chartMap f z] at made
  obtain ⟨V,openV,inV,D,hD,estimate⟩ := made.holder
  let target := (extChartAt (𝓘(ℝ,WithLp 2 (E×F))) z).target
  refine ⟨V∩target,openV.inter (isOpen_extChartAt_target z),
    ⟨inV,mem_extChartAt_target z⟩,?_,D,hD,?_⟩
  · intro y hy
    exact ⟨hy.2,by simp [chartAt_self_eq]⟩
  · intro y hy w hw
    exact estimate y hy.1 w hw.1

@[expose] def secondCoordinateMap : WithLp 2 (E×F) →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ E F).comp
    (LinearRechartedManifold.hilbertProductEquiv (A:=E) (B:=F)).symm.toContinuousLinearMap

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
theorem second_coordinate_center (z:X×Y) :
    secondCoordinateMap (extChartAt (𝓘(ℝ,WithLp 2 (E×F))) z z)=
      extChartAt (𝓘(ℝ,F)) z.2 z.2 := by
  simp only [secondCoordinateMap,extChartAt,mfld_simps]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
theorem second_chartMap (f:Y→G) (z:X×Y) :
    chartMap (E:=WithLp 2 (E×F)) (F:=G) (fun p:X×Y=>f p.2) z =
      chartMap (E:=F) (F:=G) f z.2 ∘ secondCoordinateMap (E:=E) (F:=F) := by
  simp only [chartMap,secondCoordinateMap,extChartAt,mfld_simps,Function.comp_def]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold (𝓘(ℝ,E)) ∞ X] [IsManifold (𝓘(ℝ,F)) ∞ Y] in
/-- No product regularity or Holder bound is assumed. -/
theorem Regular.hilbert_snd {r:ℝ} {f:Y→G} (hf:Regular (E:=F) (F:=G) r f) :
    Regular (E:=WithLp 2 (E×F)) (F:=G) r (fun z:X×Y=>f z.2) := by
  refine ⟨hf.nonnegative,hf.differentiable.comp
    ((HilbertProductDifferential.smooth_snd (E:=E) (F:=F) (X:=X) (Y:=Y)).of_le (by simp)),?_⟩
  intro unequal z
  have smooth : ContDiffAt ℝ (⌊r⌋₊:ℕ) (chartMap (E:=F) (F:=G) f z.2)
      (extChartAt (𝓘(ℝ,F)) z.2 z.2) := by
    simpa only [chartMap,ModelWithCorners.range_eq_univ,contDiffWithinAt_univ] using
      (contMDiffAt_iff.mp (hf.differentiable.contMDiffAt (x:=z.2))).2
  obtain ⟨U,openU,inU,_inside,C,hC,bound⟩ := hf.holder unequal z.2
  have jet : JetAt ⌊r⌋₊ (r-(⌊r⌋₊:ℝ)) (chartMap (E:=F) (F:=G) f z.2)
      (secondCoordinateMap (E:=E) (F:=F) (extChartAt (𝓘(ℝ,WithLp 2 (E×F))) z z)) := by
    rw [second_coordinate_center]
    exact ⟨smooth,U,openU,inU,C,hC,bound⟩
  have made := jet.comp_linear (sub_nonneg.mpr (Nat.floor_le hf.nonnegative))
    (secondCoordinateMap (E:=E) (F:=F))
  rw [←second_chartMap f z] at made
  obtain ⟨V,openV,inV,D,hD,estimate⟩ := made.holder
  let target := (extChartAt (𝓘(ℝ,WithLp 2 (E×F))) z).target
  refine ⟨V∩target,openV.inter (isOpen_extChartAt_target z),
    ⟨inV,mem_extChartAt_target z⟩,?_,D,hD,?_⟩
  · intro y hy
    exact ⟨hy.2,by simp [chartAt_self_eq]⟩
  · intro y hy w hw
    exact estimate y hy.1 w hw.1

end LeanShared.FractionalManifoldRegularity
