module

public import LeanShared.Dynamics.HyperbolicBoundedOrbits
public import LeanShared.Geometry.CompactRiemannianCrossMFDeriv

/-! An actual C1 semiconjugacy maps stable tangent vectors into stable
tangent vectors. Compactness supplies the derivative bound; none is assumed. -/
public noncomputable section
open Set Function IsManifold Bundle
open scoped Manifold ContDiff
namespace LeanShared.HyperbolicBasicSet
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  {T:X≃ₜX} {S:Y≃ₜY} {K:Set X} {L:Set Y}

theorem HyperbolicData.stable_map_semiconjugacy
    (a:HyperbolicData (E:=E) T K) (b:HyperbolicData (E:=F) S L)
    (forwardT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (forwardS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (inverseS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm)
    (f:X→Y) (smooth:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f)
    (maps:MapsTo f K L) (commutes:Semiconj f (T:X→X) (S:Y→Y))
    (x:X) (hx:x∈K) (v:TangentSpace (𝓘(ℝ,E)) x) (hv:v∈a.stable x) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x v ∈ b.stable (f x) := by
  obtain ⟨B,hB,bound⟩ := CompactRiemannianCrossMFDeriv.exists_norm_bound f smooth K a.compact
  have differentiable := smooth.mdifferentiable one_ne_zero
  apply b.mem_stable_of_bounded forwardS inverseS (f x) (maps hx) _ (B*a.constant*‖v‖)
  intro n
  have iterT := DiffeomorphismIterates.mdifferentiable_iterate (T:X→X) forwardT n
  have iterS := DiffeomorphismIterates.mdifferentiable_iterate (S:Y→Y) forwardS n
  have equality : f ∘ (T:X→X)^[n] = (S:Y→Y)^[n] ∘ f :=
    funext (commutes.iterate_right n).eq
  have chainT := mfderiv_comp x (differentiable _) (iterT x)
  have chainS := mfderiv_comp x (iterS _) (differentiable x)
  have derivativeEquality :
      ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (f ∘ (T:X→X)^[n]) x v‖ =
      ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) ((S:Y→Y)^[n] ∘ f) x v‖ := by
    rw [equality]
  have left := congrArg (fun A=>‖A v‖) chainT
  have right := congrArg (fun A=>‖A v‖) chainS
  have image := right.symm.trans (derivativeEquality.symm.trans left)
  simp only [ContinuousLinearMap.comp_apply] at image
  have member : (T:X→X)^[n] x ∈ K := by
    apply (show MapsTo (T:X→X) K K from fun y hy=>by
      rw [←a.invariant]; exact mem_image_of_mem T hy).iterate n hx
  have estimate := a.stable_bound n x hx v hv
  have power : a.contraction^n ≤ 1 := pow_le_one₀ a.contraction_pos.le a.contraction_lt_one.le
  have stableBound : ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T:X→X)^[n]) x v‖ ≤ a.constant*‖v‖ :=
    estimate.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right a.constant_pos.le power) (norm_nonneg _))
  rw [image]
  exact ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f ((T:X→X)^[n] x)).le_opNorm _).trans
    ((mul_le_mul (bound _ member) stableBound (norm_nonneg _) hB.le).trans_eq (by ring))

theorem HyperbolicData.unstable_map_semiconjugacy
    (a:HyperbolicData (E:=E) T K) (b:HyperbolicData (E:=F) S L)
    (inverseT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (forwardS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (inverseS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm)
    (f:X→Y) (smooth:ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,F)) 1 f)
    (maps:MapsTo f K L) (commutes:Semiconj f (T:X→X) (S:Y→Y))
    (x:X) (hx:x∈K) (v:TangentSpace (𝓘(ℝ,E)) x) (hv:v∈a.unstable x) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f x v ∈ b.unstable (f x) := by
  obtain ⟨B,hB,bound⟩ := CompactRiemannianCrossMFDeriv.exists_norm_bound f smooth K a.compact
  have differentiable := smooth.mdifferentiable one_ne_zero
  apply b.mem_unstable_of_bounded forwardS inverseS (f x) (maps hx) _ (B*a.constant*‖v‖)
  have reverseCommutes : Semiconj f (T.symm:X→X) (S.symm:Y→Y) := by
    intro y
    apply S.injective
    rw [S.apply_symm_apply,←commutes (T.symm y),T.apply_symm_apply]
  intro n
  have iterT := DiffeomorphismIterates.mdifferentiable_iterate (T.symm:X→X) inverseT n
  have iterS := DiffeomorphismIterates.mdifferentiable_iterate (S.symm:Y→Y) inverseS n
  have equality : f ∘ (T.symm:X→X)^[n] = (S.symm:Y→Y)^[n] ∘ f :=
    funext (reverseCommutes.iterate_right n).eq
  have chainT := mfderiv_comp x (differentiable _) (iterT x)
  have chainS := mfderiv_comp x (iterS _) (differentiable x)
  have derivativeEquality :
      ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) (f ∘ (T.symm:X→X)^[n]) x v‖ =
      ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) ((S.symm:Y→Y)^[n] ∘ f) x v‖ := by
    rw [equality]
  have left := congrArg (fun A=>‖A v‖) chainT
  have right := congrArg (fun A=>‖A v‖) chainS
  have image := right.symm.trans (derivativeEquality.symm.trans left)
  simp only [ContinuousLinearMap.comp_apply] at image
  have member : (T.symm:X→X)^[n] x ∈ K := by
    have reverseMaps : MapsTo (T.symm:X→X) K K := by
      intro y hy
      rw [←a.invariant] at hy
      obtain ⟨z,hz,rfl⟩ := hy
      simpa only [T.symm_apply_apply] using hz
    exact reverseMaps.iterate n hx
  have estimate := a.unstable_bound n x hx v hv
  have power : a.contraction^n ≤ 1 := pow_le_one₀ a.contraction_pos.le a.contraction_lt_one.le
  have stableBound : ‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ((T.symm:X→X)^[n]) x v‖ ≤ a.constant*‖v‖ :=
    estimate.trans (mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right a.constant_pos.le power) (norm_nonneg _))
  rw [image]
  exact ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,F)) f ((T.symm:X→X)^[n] x)).le_opNorm _).trans
    ((mul_le_mul (bound _ member) stableBound (norm_nonneg _) hB.le).trans_eq (by ring))

end LeanShared.HyperbolicBasicSet
