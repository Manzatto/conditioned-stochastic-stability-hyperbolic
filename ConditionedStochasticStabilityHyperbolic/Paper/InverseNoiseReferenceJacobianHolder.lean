module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseInverseHolder
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseNoiseReferenceJacobian
public import LeanShared.Geometry.FiniteSmoothReferenceJacobianHolder
public import LeanShared.Geometry.FiniteSmoothReferenceJacobianBound
import Mathlib.Tactic

/-! Actual Holder controls for the computed inverse Jacobian of the ORIGINAL
regular-noise family. Chart capture, derivative bounds and reference-density
normalizations are proved; no inverse Jacobian regularity input is supplied. -/
public noncomputable section
set_option maxHeartbeats 2400000
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Metric MeasureTheory Measure
open scoped Topology Manifold ContDiff NNReal

theorem InverseFamily.referenceJacobian_local_holder
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r a : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (s : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (ha : 0 < a) (ha1 : a < 1) (lower : a+1 < r)
    (regular : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (inside : y ∈ d.target) (target : T.symm (d.symm y) ∈ c.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ≥0, ∃ window : η ≤ J.window, 0 < η ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ η) (control : cube (ι := ι) ε),
      ∀ q ∈ closedBall y δ, ∀ z ∈ closedBall y δ,
        |s.jacobian (J.homeomorph ε hp (hw.trans window) control) (d.symm q)-
          s.jacobian (J.homeomorph ε hp (hw.trans window) control) (d.symm z)| ≤
            C * ‖q-z‖^a := by
  obtain ⟨δj,hδj,ηj,hηj,wj,B0,B1,H,hB0,hB1,hH,jets⟩ :=
    J.local_jet_controls ha ha1 lower regular inverse c d hc hd y inside target
  let center := c (T.symm (d.symm y))
  obtain ⟨R,hR,sourceR⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source target))
  let ρ := R/2
  have hρ : 0 < ρ := half_pos hR
  let L := closedBall center ρ
  have sourceL : L ⊆ c.target := (closedBall_subset_ball (half_lt_self hR)).trans sourceR
  let U := c.source ∩ c ⁻¹' ball center ρ
  have openU : IsOpen U := c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball
  have inU : T.symm (d.symm y) ∈ U := ⟨target,mem_ball_self hρ⟩
  have near : (T.symm ∘ d.symm) ⁻¹' U ∈ 𝓝 y :=
    (T.symm.continuous.continuousAt.comp (d.continuousAt_symm inside)).preimage_mem_nhds (openU.mem_nhds inU)
  obtain ⟨R0,hR0,source0⟩ := Metric.mem_nhds_iff.mp (inter_mem (d.open_target.mem_nhds inside) near)
  let δ := min (R0/2) (min δj (1/2))
  have hδ : 0 < δ := lt_min (half_pos hR0) (lt_min hδj (by norm_num))
  let K := closedBall y δ
  have smallK : K ⊆ closedBall y δj := closedBall_subset_closedBall (le_trans (min_le_right _ _) (min_le_left _ _))
  have subK : K ⊆ d.target ∩ (T.symm ∘ d.symm) ⁻¹' U :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hR0))).trans source0
  have sourceK : K ⊆ d.target := fun q hq => (subK hq).1
  have compactStarts : IsCompact (d.symm '' K) := (isCompact_closedBall y δ).image_of_continuousOn
    (d.continuousOn_symm.mono sourceK)
  obtain ⟨ηc,hηc,wc,capture⟩ := J.exists_uniform_target (d.symm '' K) U compactStarts openU
    (by rintro _ ⟨q,hq,rfl⟩; exact (subK hq).2)
  let η := min ηj ηc
  have hη : 0 < η := lt_min hηj hηc
  have window : η ≤ J.window := (min_le_left _ _).trans wj
  let P := Σ ε : {ε : ℝ≥0 // 0 < ε ∧ ε ≤ η}, cube (ι := ι) ε.val
  let family : P → M ≃ₜ M := fun p => J.homeomorph p.1.val p.1.property.1
    (p.1.property.2.trans window) p.2
  have captured (p : P) q (hq : q ∈ K) : (family p).symm (d.symm q) ∈ U :=
    capture p.1.val p.1.property.1 (p.1.property.2.trans (min_le_right _ _)) p.2 ⟨q,hq,rfl⟩
  have diameter q (hq : q ∈ K) z (hz : z ∈ K) : dist q z ≤ 1 := by
    have qbound : dist q y ≤ δ := hq
    have zbound : dist y z ≤ δ := by have actual : dist z y ≤ δ := hz; rwa [dist_comm] at actual
    have half : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_right _ _)
    exact (dist_triangle q y z).trans ((add_le_add qbound zbound).trans (by linarith))
  let B : ℝ≥0 := ⟨B1,hB1⟩
  have actualJets (p : P) := jets p.1.val p.1.property.1
    (p.1.property.2.trans (min_le_left _ _)) p.2
  obtain ⟨C,hC,bound⟩ := s.jacobian_local_holder μ family
    (fun p => J.forward_contMDiff p.1.val p.1.property.1 (p.1.property.2.trans window) p.2)
    (fun p => J.map_contMDiff p.1.val p.1.property.1 (p.1.property.2.trans window) p.2)
    c d hc hd K L (isCompact_closedBall y δ) (convex_closedBall y δ) sourceK
    (isCompact_closedBall center ρ) (convex_closedBall center ρ) sourceL diameter
    a B1 H ha1.le hH B (fun p q hq => (captured p q hq).1)
    (fun p q hq => ball_subset_closedBall (captured p q hq).2)
    (fun p => Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq => ((actualJets p).1 q (smallK hq)).1.differentiableAt (by simp))
      (fun q hq => by exact_mod_cast ((actualJets p).1 q (smallK hq)).2.2)
      (convex_closedBall y δ))
    (fun p q hq => ((actualJets p).1 q (smallK hq)).2.2)
    (fun p q hq z hz => by
      change ‖fderiv ℝ (c ∘ (fun x => J.map p.1.val (p.2.val,x)) ∘ d.symm) q-
        fderiv ℝ (c ∘ (fun x => J.map p.1.val (p.2.val,x)) ∘ d.symm) z‖ ≤ _
      simpa only [dist_eq_norm] using (actualJets p).2 q (smallK hq) z (smallK hz))
  refine ⟨δ,hδ,η,window,hη,C,hC,?_⟩
  intro ε hp hw control q hq z hz
  simpa only [dist_eq_norm] using bound (⟨⟨ε,hp,hw⟩,control⟩ : P) q hq z hz


theorem InverseFamily.referenceJacobian_local_controls
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MetricSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    {T : M ≃ₜ M} {r a : ℝ} {F : Maps (E := E) (ι := ι) T r}
    (J : InverseFamily F) (s : LeanShared.FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (μ : Measure E) [IsAddHaarMeasure μ]
    (ha : 0 < a) (ha1 : a < 1) (lower : a+1 < r)
    (regular : LeanShared.FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (y : E) (inside : y ∈ d.target) (target : T.symm (d.symm y) ∈ c.source) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ η : ℝ≥0, ∃ window : η ≤ J.window, 0 < η ∧ ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (ε : ℝ≥0) (hp : 0 < ε) (hw : ε ≤ η) (control : cube (ι := ι) ε),
      ∀ q ∈ closedBall y δ,
        |s.jacobian (J.homeomorph ε hp (hw.trans window) control) (d.symm q)| ≤ B ∧
        ∀ z ∈ closedBall y δ,
        |s.jacobian (J.homeomorph ε hp (hw.trans window) control) (d.symm q)-
          s.jacobian (J.homeomorph ε hp (hw.trans window) control) (d.symm z)| ≤
            C * ‖q-z‖^a := by
  obtain ⟨δj,hδj,ηj,hηj,wj,B0,B1,H,hB0,hB1,hH,jets⟩ :=
    J.local_jet_controls ha ha1 lower regular inverse c d hc hd y inside target
  let center := c (T.symm (d.symm y))
  obtain ⟨R,hR,sourceR⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds (c.map_source target))
  let ρ := R/2
  have hρ : 0 < ρ := half_pos hR
  let L := closedBall center ρ
  have sourceL : L ⊆ c.target := (closedBall_subset_ball (half_lt_self hR)).trans sourceR
  let U := c.source ∩ c ⁻¹' ball center ρ
  have openU : IsOpen U := c.continuousOn.isOpen_inter_preimage c.open_source isOpen_ball
  have inU : T.symm (d.symm y) ∈ U := ⟨target,mem_ball_self hρ⟩
  have near : (T.symm ∘ d.symm) ⁻¹' U ∈ 𝓝 y :=
    (T.symm.continuous.continuousAt.comp (d.continuousAt_symm inside)).preimage_mem_nhds (openU.mem_nhds inU)
  obtain ⟨R0,hR0,source0⟩ := Metric.mem_nhds_iff.mp (inter_mem (d.open_target.mem_nhds inside) near)
  let δ := min (R0/2) (min δj (1/2))
  have hδ : 0 < δ := lt_min (half_pos hR0) (lt_min hδj (by norm_num))
  let K := closedBall y δ
  have smallK : K ⊆ closedBall y δj := closedBall_subset_closedBall (le_trans (min_le_right _ _) (min_le_left _ _))
  have subK : K ⊆ d.target ∩ (T.symm ∘ d.symm) ⁻¹' U :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hR0))).trans source0
  have sourceK : K ⊆ d.target := fun q hq => (subK hq).1
  have compactStarts : IsCompact (d.symm '' K) := (isCompact_closedBall y δ).image_of_continuousOn
    (d.continuousOn_symm.mono sourceK)
  obtain ⟨ηc,hηc,wc,capture⟩ := J.exists_uniform_target (d.symm '' K) U compactStarts openU
    (by rintro _ ⟨q,hq,rfl⟩; exact (subK hq).2)
  let η := min ηj ηc
  have hη : 0 < η := lt_min hηj hηc
  have window : η ≤ J.window := (min_le_left _ _).trans wj
  let P := Σ ε : {ε : ℝ≥0 // 0 < ε ∧ ε ≤ η}, cube (ι := ι) ε.val
  let family : P → M ≃ₜ M := fun p => J.homeomorph p.1.val p.1.property.1
    (p.1.property.2.trans window) p.2
  have captured (p : P) q (hq : q ∈ K) : (family p).symm (d.symm q) ∈ U :=
    capture p.1.val p.1.property.1 (p.1.property.2.trans (min_le_right _ _)) p.2 ⟨q,hq,rfl⟩
  have diameter q (hq : q ∈ K) z (hz : z ∈ K) : dist q z ≤ 1 := by
    have qbound : dist q y ≤ δ := hq
    have zbound : dist y z ≤ δ := by have actual : dist z y ≤ δ := hz; rwa [dist_comm] at actual
    have half : δ ≤ 1/2 := (min_le_right _ _).trans (min_le_right _ _)
    exact (dist_triangle q y z).trans ((add_le_add qbound zbound).trans (by linarith))
  let B : ℝ≥0 := ⟨B1,hB1⟩
  have actualJets (p : P) := jets p.1.val p.1.property.1
    (p.1.property.2.trans (min_le_left _ _)) p.2
  obtain ⟨C,hC,bound⟩ := s.jacobian_local_holder μ family
    (fun p => J.forward_contMDiff p.1.val p.1.property.1 (p.1.property.2.trans window) p.2)
    (fun p => J.map_contMDiff p.1.val p.1.property.1 (p.1.property.2.trans window) p.2)
    c d hc hd K L (isCompact_closedBall y δ) (convex_closedBall y δ) sourceK
    (isCompact_closedBall center ρ) (convex_closedBall center ρ) sourceL diameter
    a B1 H ha1.le hH B (fun p q hq => (captured p q hq).1)
    (fun p q hq => ball_subset_closedBall (captured p q hq).2)
    (fun p => Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun q hq => ((actualJets p).1 q (smallK hq)).1.differentiableAt (by simp))
      (fun q hq => by exact_mod_cast ((actualJets p).1 q (smallK hq)).2.2)
      (convex_closedBall y δ))
    (fun p q hq => ((actualJets p).1 q (smallK hq)).2.2)
    (fun p q hq z hz => by
      change ‖fderiv ℝ (c ∘ (fun x => J.map p.1.val (p.2.val,x)) ∘ d.symm) q-
        fderiv ℝ (c ∘ (fun x => J.map p.1.val (p.2.val,x)) ∘ d.symm) z‖ ≤ _
      simpa only [dist_eq_norm] using (actualJets p).2 q (smallK hq) z (smallK hz))
  obtain ⟨Bv,hBv,value⟩ := s.jacobian_local_bound μ family
    (fun p => J.forward_contMDiff p.1.val p.1.property.1 (p.1.property.2.trans window) p.2)
    (fun p => J.map_contMDiff p.1.val p.1.property.1 (p.1.property.2.trans window) p.2)
    c d hc hd K L (isCompact_closedBall y δ) sourceK (isCompact_closedBall center ρ) sourceL B1
    (fun p q hq => (captured p q hq).1)
    (fun p q hq => ball_subset_closedBall (captured p q hq).2)
    (fun p q hq => ((actualJets p).1 q (smallK hq)).2.2)
  refine ⟨δ,hδ,η,window,hη,Bv,C,hBv,hC,?_⟩
  intro ε hp hw control q hq
  refine ⟨value (⟨⟨ε,hp,hw⟩,control⟩ : P) q hq,?_⟩
  intro z hz
  simpa only [dist_eq_norm] using bound (⟨⟨ε,hp,hw⟩,control⟩ : P) q hq z hz

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
