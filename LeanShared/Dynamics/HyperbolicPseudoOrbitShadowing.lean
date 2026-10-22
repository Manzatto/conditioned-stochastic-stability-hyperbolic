module
public import LeanShared.Geometry.PseudoReferenceNonlinearBlocks
public import LeanShared.Geometry.PseudoReferenceForcing
public import LeanShared.Geometry.PseudoReferenceDecodeBounds
public import LeanShared.Dynamics.LocalHyperbolicShadowing

/-! Bilateral manifold shadowing is constructed from actual hyperbolicity,
coherent finite charts, derivative bounds and the bilateral contraction. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff NNReal BoundedContinuousFunction
open PseudoReferenceCoordinateMaps CenteredManifoldCoordinates

set_option maxHeartbeats 2400000 in
theorem HyperbolicData.pseudo_reference_shadowing
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ:Set M} {h:HyperbolicData (E:=E) T Λ}
    (d:PseudoReferenceGeometry h) (a:IsometricFraming h)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (ε:ℝ) (positiveε:0<ε) :
    ∃η:ℝ,0<η ∧ ∀reference:ℤ→Λ,
      (∀n,dist ((T^d.blockLength) (reference (n+1)).val) (reference n).val<η) →
      ∃orbit:ℤ→M,
        (∀n,(T^d.blockLength) (orbit (n+1))=orbit n) ∧
        ∀n,dist (orbit n) (reference n).val<ε := by
  obtain ⟨B,positiveB,bounds⟩ := a.exists_uniform_bound
  obtain ⟨r,positiveR,η0,positiveη0,blocks⟩ :=
    exists_nonlinear_blocks d a forward (1/8) (by norm_num)
  obtain ⟨r0,positiveR0,decodeSmall⟩ := exists_decode_radius d a.whole positiveB bounds ε positiveε
  let radius := min r r0
  have positiveRadius : 0<radius := lt_min positiveR positiveR0
  obtain ⟨η1,positiveη1,forcing⟩ := exists_forcing_window d a.whole positiveB bounds
    (T^d.blockLength:M≃ₜM) (radius/4) (by positivity)
  refine ⟨min η0 η1,lt_min positiveη0 positiveη1,fun reference step=>?_⟩
  have pair (n:ℤ) := blocks (reference (n+1)) (reference n)
    ((step n).trans_le (min_le_left _ _))
  choose stable unstable stableBound unstableBound estimates using pair
  let maps := fun n:ℤ=>centered (linear d a.whole (reference (n+1)))
    (linear d a.whole (reference n))
    (chart d (reference (n+1)) (reference (n+1)).val)
    (chart d (reference n) (reference n).val)
    (chart d (reference n) ∘ (T^d.blockLength:M≃ₜM) ∘ (chart d (reference (n+1))).symm)
  have diff (n:ℤ) z (hz:‖z‖≤radius) : DifferentiableAt ℝ (maps n) z :=
    (estimates n z (hz.trans (min_le_left _ _))).2.2.1
  have derivative (n:ℤ) z (hz:‖z‖≤radius) :
      ‖fderiv ℝ (maps n) z-(unstable n).toContinuousLinearMap.prodMap (stable n).toContinuousLinearMap‖≤(1/8:ℝ) :=
    (estimates n z (hz.trans (min_le_left _ _))).2.2.2
  have origin (n:ℤ) : ‖maps n 0‖≤radius/4 :=
    (forcing _ _ ((step n).trans_le (min_le_right _ _))).2
  obtain ⟨z,zBound,zStep,_⟩ := LocalHyperbolicShadowing.exists_orbit maps unstable
    (fun n=>(stable n).toContinuousLinearMap) ⟨1/4,by norm_num⟩ ⟨1/8,by norm_num⟩
    (by change (1/4+1/8*2:ℝ)<1; norm_num) unstableBound stableBound radius positiveRadius diff derivative
    (radius/4) origin (by change (1/4+1:ℝ)*(radius/4)≤(1-(1/4+1/8*2))*radius; nlinarith)
  have bounded (n:ℤ) : ‖z n‖≤radius := by
    apply (z.norm_coe_le_norm n).trans
    apply zBound.trans
    change ((1/4:ℝ)+1)*(radius/4)/(1-(1/4+1/8*2))≤radius
    norm_num
    nlinarith
  refine ⟨fun n=>decode d a.whole (reference n) (z n),fun n=>?_,fun n=>?_⟩
  · have valid := (estimates n (z (n+1)) ((bounded (n+1)).trans (min_le_left _ _))).2.1
    have actual : coordinate d a.whole (reference n)
        ((T^d.blockLength) (decode d a.whole (reference (n+1)) (z (n+1))))=z n := zStep n
    have same := congrArg (decode d a.whole (reference n)) actual
    exact (decode_coordinate d a.whole (reference n) _ valid).symm.trans same
  · exact (decodeSmall (reference n) (z n) ((bounded n).trans (min_le_right _ _))).2

end LeanShared.HyperbolicBasicSet
