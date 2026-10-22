module
public import LeanShared.Geometry.FractionalJetCharacterization
public import LeanShared.Geometry.LocalFractionalJetFullComposition
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! Full real-order map jets in arbitrary genuine smooth source and target
charts. Both actual nonlinear chart transitions are handled; no extra
derivative or globally smooth extension of a partial chart is assumed. -/
public noncomputable section
open Set Filter IsManifold
open scoped Topology Manifold ContDiff
namespace LeanShared.FractionalManifoldRegularity
universe u
variable {E F : Type u} {M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem Regular.map_chart_jet {f : M → N} {a : ℝ} {n : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (regular : Regular (E := E) (F := F) (a+n) f) (x : M) :
    JetAt n a (chartMap (E := E) (F := F) f x) (extChartAt (𝓘(ℝ, E)) x x) := by
  have floor := floor_fraction_add_nat ha.le ha1 n
  have coordinate : ContDiffAt ℝ n (chartMap (E := E) (F := F) f x)
      (extChartAt (𝓘(ℝ, E)) x x) := by
    have actual := (contMDiffAt_iff.mp (regular.differentiable.contMDiffAt (x := x))).2
    simpa only [chartMap, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ, floor] using actual
  have unequal : a+n ≠ (⌊a+n⌋₊ : ℝ) := by rw [floor]; linarith
  obtain ⟨U, openU, inU, _inside, C, hC, bound⟩ := regular.holder unequal x
  refine ⟨coordinate, U, openU, inU, C, hC, ?_⟩
  intro y hy z hz
  have actual := bound y hy z hz
  rw [floor] at actual
  simpa only [add_sub_cancel_right] using actual

theorem Regular.contDiffAt_in_charts {r : ℝ} {f : M → N}
    (regular : Regular (E := E) (F := F) r f)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N)
    (y : E) (source : y ∈ c.target) (target : f (c.symm y) ∈ d.source) :
    ContDiffAt ℝ (⌊r⌋₊ : ℕ) (d ∘ f ∘ c.symm) y := by
  have inverse := contMDiffAt_symm_of_mem_maximalAtlas hc source
  have final := contMDiffAt_of_mem_maximalAtlas hd target
  exact ((final.of_le (by simp)).comp y
    (regular.differentiable.contMDiffAt.comp y (inverse.of_le (by simp)))).contDiffAt

theorem Regular.jet_in_charts {f : M → N} {a : ℝ} {n : ℕ}
    (ha : 0 < a) (ha1 : a < 1) (regular : Regular (E := E) (F := F) (a+n) f)
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N)
    (y : E) (source : y ∈ c.target) (target : f (c.symm y) ∈ d.source) :
    JetAt n a (d ∘ f ∘ c.symm) y := by
  let x := c.symm y
  let e := extChartAt (𝓘(ℝ, E)) x
  let e' := extChartAt (𝓘(ℝ, F)) (f x)
  let A : E → E := e ∘ c.symm
  let C : E → F := chartMap (E := E) (F := F) f x
  let B : F → F := d ∘ e'.symm
  have inverse : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ c.symm y :=
    contMDiffAt_symm_of_mem_maximalAtlas hc source
  have smoothA : ContDiffAt ℝ ∞ A y :=
    (contMDiffAt_extChartAt.comp y inverse).contDiffAt
  have valueC : C (A y) = e' (f x) := by
    change e' (f (e.symm (e x))) = e' (f x)
    rw [extChartAt_to_inv]
  have smoothB : ContDiffAt ℝ ∞ B (e' (f x)) := by
    have inv : ContMDiffAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ e'.symm (e' (f x)) :=
      (contMDiffWithinAt_extChartAt_symm_target_self (I := 𝓘(ℝ, F)) (n := ∞) (f x)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, F)) (f x)).mem_nhds
          (mem_extChartAt_target (I := 𝓘(ℝ, F)) (f x)))
    have final : ContMDiffAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ d (e'.symm (e' (f x))) := by
      rw [extChartAt_to_inv]
      exact contMDiffAt_of_mem_maximalAtlas hd target
    exact (final.comp (e' (f x)) inv).contDiffAt
  have native : JetAt n a C (A y) := regular.map_chart_jet ha ha1 x
  have first := JetAt.comp_smooth n ha.le ha1.le native smoothA
  have smoothAtValue : ContDiffAt ℝ ∞ B ((C ∘ A) y) := by
    rw [Function.comp_apply, valueC]
    exact smoothB
  have combined := JetAt.smooth_comp n ha.le ha1.le smoothAtValue first
  apply combined.congr
  have nearSource : c.symm ⁻¹' e.source ∈ 𝓝 y := inverse.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source x).mem_nhds (mem_extChartAt_source x))
  have nearTarget : (f ∘ c.symm) ⁻¹' e'.source ∈ 𝓝 y :=
    (regular.differentiable.continuous.continuousAt.comp inverse.continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_source (f x)).mem_nhds (mem_extChartAt_source (f x)))
  filter_upwards [nearSource, nearTarget] with z hz hz'
  change d (e'.symm (e' (f (e.symm (e (c.symm z)))))) = d (f (c.symm z))
  have hzTarget : f (c.symm z) ∈ e'.source := hz'
  rw [e.left_inv hz, e'.left_inv hzTarget]

/-- The exact floor and fractional part used by the literal C^r class. -/
theorem Regular.holder_jet_in_charts {r : ℝ} {f : M → N}
    (regular : Regular (E := E) (F := F) r f) (unequal : r ≠ (⌊r⌋₊ : ℝ))
    (c : OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph N F)
    (hc : c ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ, F)) ∞ N)
    (y : E) (source : y ∈ c.target) (target : f (c.symm y) ∈ d.source) :
    JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (d ∘ f ∘ c.symm) y := by
  have positive : 0 < r-(⌊r⌋₊ : ℝ) := sub_pos.mpr
    (lt_of_le_of_ne (Nat.floor_le regular.nonnegative) (Ne.symm unequal))
  have subunit : r-(⌊r⌋₊ : ℝ) < 1 := by linarith [Nat.lt_floor_add_one r]
  have order : (r-(⌊r⌋₊ : ℝ))+(⌊r⌋₊ : ℝ) = r := sub_add_cancel _ _
  have actual : Regular (E := E) (F := F) ((r-(⌊r⌋₊ : ℝ))+(⌊r⌋₊ : ℝ)) f := by
    rw [order]
    exact regular
  exact actual.jet_in_charts positive subunit c d hc hd y source target

end LeanShared.FractionalManifoldRegularity
