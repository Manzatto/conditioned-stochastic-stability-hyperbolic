module
public import LeanShared.Dynamics.BasicHyperbolicFiniteShadowing
public import LeanShared.Dynamics.CompactMixingChains
public import LeanShared.Dynamics.BasicHyperbolicSpecification
public import LeanShared.Dynamics.OrbitWordReversal
public import LeanShared.Dynamics.EntireOrbitFiniteTimes

/-! A single gap, chosen before the number and lengths of orbit segments,
lets an actual orbit in the basic set trace every prescribed segment.
Times are written in the backward indexing of the bilateral solver. -/
public noncomputable section
namespace LeanShared.HyperbolicBasicSet
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff
open FiniteOrbitWordAssembly BilateralHomeomorphismOrbit

theorem BasicData.finite_specification
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M]
    [RiemannianBundle (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x:M=>TangentSpace (𝓘(ℝ,E)) x)]
    {T:M≃ₜM} {Λ V:Set M} (b:BasicData (E:=E) T Λ V)
    (forward:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (mixing:MixingOn T Λ) (ε:ℝ) (positiveε:0<ε) :
    ∃gap:ℕ,0<gap ∧ ∀length:ℕ→ℕ,∀points:ℕ→Λ,∀k:ℕ,
      ∃z:Λ,∀i≤k,∀j≤length i,
        dist (((T:M→M)^[offset gap length i+j]) z.val)
          (((T:M→M)^[j]) (points i).val)<ε := by
  obtain ⟨gap,positiveGap,back⟩ := b.backward_specification forward inverse mixing ε positiveε
  let S:=invariantCoreHomeomorphism T Λ b.hyperbolic.invariant
  have equivariant : Function.Semiconj (Subtype.val:Λ→M) S T := fun _=>rfl
  have powers (n:ℕ) (x:Λ) : ((S^n) x).val=((T:M→M)^[n]) x.val := by
    rw [DiffeomorphismIterates.coe_pow]
    exact (equivariant.iterate_right n).eq x
  refine ⟨gap,positiveGap,fun length points k=>?_⟩
  let reversedLength:=reversed length k
  let reversedPoints:=fun i:ℕ=>(S^(length (k-i))) (points (k-i))
  obtain ⟨p,step,close⟩ := back reversedLength reversedPoints k
  let total:=ending gap length k
  refine ⟨p (total:ℤ),fun i hi j hj=>?_⟩
  let r:=k-i
  have reflect:k-r=i := Nat.sub_sub_self hi
  have lengthEq:reversedLength r=length i := by
    change length (k-r)=length i
    rw [reflect]
  have rBound:r≤k := Nat.sub_le _ _
  have near := close r rBound (length i-j) (by rw [lengthEq]; omega)
  let m:=offset gap reversedLength r+(length i-j)
  let t:=offset gap length i+j
  have schedule:offset gap length i+offset gap reversedLength r+length i=total :=
    offset_reversal gap length hi
  have sum:m+t=total := by dsimp only [m,t]; omega
  have actualTime := EntireOrbitFiniteTimes.iterate_between (T:M→M) (fun n=>(p n).val) step m t
  rw [sum] at actualTime
  have endPoint:(reversedPoints r).val=((T:M→M)^[length i]) (points i).val := by
    change ((S^(length (k-r))) (points (k-r))).val=_
    rw [reflect]
    exact powers _ _
  have segment:((T.symm:M→M)^[length i-j]) (reversedPoints r).val=
      ((T:M→M)^[j]) (points i).val := by
    rw [endPoint]
    have factor:((T:M→M)^[length i]) (points i).val=
        ((T:M→M)^[length i-j]) (((T:M→M)^[j]) (points i).val) := by
      rw [←Function.iterate_add_apply,Nat.sub_add_cancel hj]
    exact (congrArg ((T.symm:M→M)^[length i-j]) factor).trans
      ((Function.LeftInverse.iterate (fun x=>T.symm_apply_apply x) (length i-j)) _)
  change dist (((T:M→M)^[t]) (p (total:ℤ)).val) (((T:M→M)^[j]) (points i).val)<ε
  rw [actualTime]
  simpa only [m,segment] using near

end LeanShared.HyperbolicBasicSet
