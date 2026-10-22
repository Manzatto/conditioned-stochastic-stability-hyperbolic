module
public import LeanShared.MeasureTheory.CoordinateJacobianDensity
public import LeanShared.Analysis.ParametricPartialDerivativeContinuity
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Joint control/state continuity of a transported chart bump's actual
inverse Jacobian density. The state derivative is constructed from joint C1;
compact support removes jumps at the other chart boundary. -/
public noncomputable section
namespace LeanShared.ParametricChartJacobianDensity
open Set Filter IsManifold
open scoped Topology Manifold ContDiff

@[expose] def density
    {A E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    (e d : OpenPartialHomeomorph M E) (p : E → ℝ) (Φ : A × M → M) : A × E → ℝ := by
  classical
  exact fun q => if q.2 ∈ d.target ∧ Φ (q.1,d.symm q.2) ∈ e.source then
    |(fderiv ℝ (fun y => e (Φ (q.1,d.symm y))) q.2).det| * p (e (Φ (q.1,d.symm q.2))) else 0

set_option maxHeartbeats 2400000 in
theorem continuousOn
    {A E M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    (e d : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (p : E → ℝ) (continuous : Continuous p) (compact : HasCompactSupport p)
    (support : tsupport p ⊆ e.target)
    (Φ : A × M → M) (O : Set A) (openO : IsOpen O)
    (joint : ContMDiffOn ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1 Φ (O ×ˢ univ)) :
    ContinuousOn (density e d p Φ) (O ×ˢ d.target) := by
  classical
  let K := e.symm '' tsupport p
  have compactK : IsCompact K := compact.isCompact.image_of_continuousOn
    (e.symm.continuousOn.mono support)
  have insideK : K ⊆ e.source := by
    rintro _ ⟨x,hx,rfl⟩
    exact e.map_target (support hx)
  intro q hq
  have inverseChart : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 d.symm q.2 :=
    (contMDiffAt_symm_of_mem_maximalAtlas (n := ∞) hd hq.2).of_le (by decide)
  have first : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) 1
      (fun z : A × E => (z.1,d.symm z.2)) q :=
    contMDiffAt_fst.prodMk (inverseChart.comp q contMDiffAt_snd)
  have phi : ContMDiffAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) 1
      (fun z : A × E => Φ (z.1,d.symm z.2)) q :=
    ((joint (q.1,d.symm q.2) ⟨hq.1,mem_univ _⟩).contMDiffAt
      ((openO.prod isOpen_univ).mem_nhds ⟨hq.1,mem_univ _⟩)).comp q first
  by_cases inside : Φ (q.1,d.symm q.2) ∈ e.source
  · have last : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 e (Φ (q.1,d.symm q.2)) :=
      (contMDiffAt_of_mem_maximalAtlas (n := ∞) he inside).of_le (by decide)
    have coordinate : ContDiffAt ℝ 1 (fun z : A × E => e (Φ (z.1,d.symm z.2))) q := by
      have raw := last.comp q phi
      rw [←modelWithCornersSelf_prod, chartedSpaceSelf_prod] at raw
      exact raw.contDiffAt
    have derivative := ParametricPartialDerivativeContinuity.continuousAt _ q coordinate
    have determinant := ContinuousLinearMap.continuous_det.continuousAt.comp derivative
    have product := determinant.abs.mul (continuous.continuousAt.comp coordinate.continuousAt)
    apply ContinuousAt.continuousWithinAt
    apply product.congr_of_eventuallyEq
    have near := Filter.Eventually.and
      ((continuous_snd.continuousAt).preimage_mem_nhds (d.open_target.mem_nhds hq.2))
      (phi.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds inside))
    filter_upwards [near] with z hz
    exact ite_eq_left hz
  · have outside : Φ (q.1,d.symm q.2) ∉ K := fun h => inside (insideK h)
    have near : ∀ᶠ z : A × E in 𝓝 q, z.2 ∈ d.target ∧ Φ (z.1,d.symm z.2) ∉ K :=
      Filter.Eventually.and
        (continuous_snd.continuousAt.preimage_mem_nhds (d.open_target.mem_nhds hq.2))
        (phi.continuousAt.preimage_mem_nhds (compactK.isClosed.isOpen_compl.mem_nhds outside))
    have zero : density e d p Φ =ᶠ[𝓝 q] (fun _ => 0) := by
      filter_upwards [near] with z hz
      by_cases member : Φ (z.1,d.symm z.2) ∈ e.source
      · have vanish : p (e (Φ (z.1,d.symm z.2))) = 0 := by
          by_contra nonzero
          have belongs : e (Φ (z.1,d.symm z.2)) ∈ tsupport p :=
            subset_closure (Function.mem_support.mpr nonzero)
          exact hz.2 ⟨_,belongs,e.left_inv member⟩
        change (if z.2 ∈ d.target ∧ Φ (z.1,d.symm z.2) ∈ e.source then _ else _) = 0
        rw [ite_eq_left ⟨hz.1,member⟩,vanish,mul_zero]
      · exact ite_eq_right (fun h => member h.2)
    exact continuousAt_const.congr_of_eventuallyEq zero |>.continuousWithinAt

end LeanShared.ParametricChartJacobianDensity
