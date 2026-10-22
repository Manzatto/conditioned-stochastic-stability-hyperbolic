module
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! The actual derivative of a parameter-preserving endpoint map is
bijective exactly when its state derivative is bijective. The parameter
and state tangent fibers are retained separately. -/
public section
namespace LeanShared.ParametricSkewDifferential
open Set IsManifold
open scoped Manifold

theorem bijective
    {A E P M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P] [ChartedSpace A P] [TopologicalSpace M] [ChartedSpace E M]
    {F : P × M → M} {a : P} {x : M}
    (smooth : MDifferentiableAt ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F (a,x))
    (rank : Function.Bijective (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun z => F (a,z)) x)) :
    Function.Bijective (mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) ((𝓘(ℝ,A)).prod (𝓘(ℝ,E)))
      (fun p : P × M => (p.1,F p)) (a,x)) := by
  rw [mfderiv_prodMk mdifferentiableAt_fst smooth]
  constructor
  · intro v w equal
    change TangentSpace (𝓘(ℝ,A)) a × TangentSpace (𝓘(ℝ,E)) x at v w
    have first : v.1 = w.1 := by
      have equality := congrArg Prod.fst equal
      change mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,A)) Prod.fst (a,x) v =
        mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,A)) Prod.fst (a,x) w at equality
      rw [mfderiv_fst] at equality
      exact equality
    apply Prod.ext first
    apply rank.1
    have second := congrArg Prod.snd equal
    change mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F (a,x) v =
      mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F (a,x) w at second
    have expanded := (mfderiv_prod_eq_add_apply (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E)) (f := F) (p := (a,x)) (v := v) smooth).symm.trans
      (second.trans (mfderiv_prod_eq_add_apply (I := 𝓘(ℝ,A)) (I' := 𝓘(ℝ,E)) (I'' := 𝓘(ℝ,E)) (f := F) (p := (a,x)) (v := w) smooth))
    rw [first] at expanded
    exact add_left_cancel expanded
  · intro y
    change TangentSpace (𝓘(ℝ,A)) a × TangentSpace (𝓘(ℝ,E)) (F (a,x)) at y
    obtain ⟨v,hv⟩ := rank.2 (y.2 - mfderiv (𝓘(ℝ,A)) (𝓘(ℝ,E)) (fun b => F (b,x)) a y.1)
    refine ⟨(y.1,v),Prod.ext ?_ ?_⟩
    · change mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,A)) Prod.fst (a,x) (y.1,v) = y.1
      rw [mfderiv_fst]
      rfl
    · change mfderiv ((𝓘(ℝ,A)).prod (𝓘(ℝ,E))) (𝓘(ℝ,E)) F (a,x) (y.1,v) = y.2
      erw [mfderiv_prod_eq_add_apply smooth,hv]
      rw [add_comm,sub_add_cancel]

end LeanShared.ParametricSkewDifferential
