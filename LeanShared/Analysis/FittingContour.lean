module

public import LeanShared.Analysis.FittingBlocks
public import LeanShared.Analysis.FittingProjection
public import LeanShared.Analysis.BlockContour
public import LeanShared.Analysis.NilpotentContour
public import LeanShared.Analysis.ResolventContourZero
public import LeanShared.Analysis.MeromorphicFittingResolvent

/-! Actual Riesz contour projectors equal the bounded projections in a
stable Fitting decomposition. No spectral projection theorem is assumed. -/

public section
open ContinuousLinearMap Submodule Metric Set
namespace LeanShared.FittingContour

/-- Small contours of an actual nilpotent/invertible block pair are `(1,0)`. -/
theorem block_contours {K V : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (N : K →L[ℂ] K) (B : V →L[ℂ] V) (n : ℕ) (hN : N ^ n = 0) (hB : IsUnit B) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R < r →
      sphere (0 : ℂ) R ⊆ resolventSet ℂ (N.prodMap B) ∧
      RieszContourIdempotent.projector (N.prodMap B) 0 R =
        (1 : K →L[ℂ] K).prodMap (0 : V →L[ℂ] V) := by
  obtain ⟨r, hr, hcontours⟩ := ResolventContourZero.exists_zero_contours B hB
  refine ⟨r, hr, fun R hR hsmall => ?_⟩
  have resN : sphere (0 : ℂ) R ⊆ resolventSet ℂ N := by
    intro z hz
    apply MeromorphicFittingResolvent.nilpotent_resolvent N n hN z
    intro he
    subst z
    have hh : (0 : ℝ) = R := by simpa only [mem_sphere, dist_self] using hz
    exact hR.ne' hh.symm
  have resB : sphere (0 : ℂ) R ⊆ resolventSet ℂ B :=
    sphere_subset_closedBall.trans (hcontours R hR hsmall).1
  refine ⟨fun z hz => (BlockResolvent.formula N B z (resN hz) (resB hz)).1, ?_⟩
  rw [BlockContour.prodMap N B 0 R hR.le resN resB,
    NilpotentResolvent.circle_integral_eq_one N n hN R hR, (hcontours R hR hsmall).2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The actual small Riesz projector is exactly the bounded projection onto
the stabilized generalized kernel along the stabilized range. -/
theorem exists_contours (S : E →L[ℂ] E) (n : ℕ)
    (hcompl : IsTopCompl (S ^ n).ker (S ^ n).range)
    (hker : (S ^ (n + 1)).ker = (S ^ n).ker)
    (hrange : (S ^ (n + 1)).range = (S ^ n).range) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R < r →
      sphere (0 : ℂ) R ⊆ resolventSet ℂ S ∧
      RieszContourIdempotent.projector S 0 R =
        (S ^ n).ker.projectionL (S ^ n).range hcompl := by
  let K := (S ^ n).ker
  let V := (S ^ n).range
  let : CompleteSpace K := (S ^ n).isClosed_ker.isComplete.completeSpace_coe
  let : CompleteSpace V := hcompl.isClosed'.isComplete.completeSpace_coe
  obtain ⟨N, B, hN, hB, conjugation⟩ := FittingBlocks.exists_blocks S n hcompl hker hrange
  obtain ⟨r, hr, hcontours⟩ := block_contours N B n hN hB
  let e := K.prodEquivOfIsTopCompl V hcompl
  refine ⟨r, hr, fun R hR hsmall => ?_⟩
  have hblock := (hcontours R hR hsmall).1
  have resS : sphere (0 : ℂ) R ⊆ resolventSet ℂ S := by
    intro z hz
    have mapped := AlgHom.mem_resolventSet_apply e.conjContinuousAlgEquiv (hblock hz)
    rw [conjugation] at mapped
    exact mapped
  refine ⟨resS, ?_⟩
  conv_lhs => rw [← conjugation]
  rw [BlockContour.conjugate e (N.prodMap B) 0 R hR.le hblock,
    (hcontours R hR hsmall).2]
  exact FittingProjection.conjugate K V hcompl

end LeanShared.FittingContour
