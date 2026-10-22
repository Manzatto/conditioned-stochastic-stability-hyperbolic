module
public import LeanShared.Analysis.SurjectiveDifferentialNeighborhood
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Literal C1 full control rank at a point supplies an open joint neighborhood
on which all partial control differentials remain surjective. -/
public noncomputable section
namespace LeanShared.SubmersionLinearCoordinates
open Set Filter
open scoped Topology

theorem exists_control_rank_neighborhood
    {X A Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {f : X × A → Y} {x : X} {a : A}
    (smooth : ContDiffAt ℝ 1 f (x, a))
    (rank : Function.Surjective (fderiv ℝ (fun b => f (x, b)) a)) :
    ∃ O : Set (X × A), IsOpen O ∧ (x, a) ∈ O ∧ ContDiffOn ℝ 1 f O ∧
      ∀ z ∈ O, Function.Surjective (fderiv ℝ (fun b => f (z.1, b)) z.2) := by
  let D : X × A → A →L[ℝ] Y :=
    fun z => (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ X A)
  have control (z : X × A) (hz : DifferentiableAt ℝ f z) :
      fderiv ℝ (fun b => f (z.1, b)) z.2 = D z := by
    exact (hz.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right z.1 z.2)).fderiv
  have rankD : Function.Surjective (D (x, a)) := by
    rw [← control (x, a) (smooth.differentiableAt one_ne_zero)]
    exact rank
  have continuousD : ContinuousAt D (x, a) :=
    (smooth.continuousAt_fderiv one_ne_zero).clm_comp continuousAt_const
  have near := (eventually_surjective continuousD rankD).and (smooth.eventually (by decide))
  obtain ⟨O, contained, openO, member⟩ := mem_nhds_iff.mp near
  refine ⟨O, openO, member, (fun z hz => ((contained hz).2).contDiffWithinAt), ?_⟩
  intro z hz
  rw [control z ((contained hz).2.differentiableAt one_ne_zero)]
  exact (contained hz).1

end LeanShared.SubmersionLinearCoordinates
