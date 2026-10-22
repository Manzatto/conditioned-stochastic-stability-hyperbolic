module

public import LeanShared.Analysis.FittingBlocks
public import LeanShared.Analysis.NilpotentResolvent
public import LeanShared.Analysis.AnalyticResolvent
public import LeanShared.Analysis.MeromorphicBlockResolvent
public import LeanShared.Analysis.ConjugateResolvent
public import Mathlib.RingTheory.Nilpotent.Basic

/-! A topological Fitting decomposition yields the actual meromorphic
resolvent: finite Laurent nilpotent block plus analytic invertible block. -/

public section
open Filter Topology ContinuousLinearMap Submodule
namespace LeanShared.MeromorphicFittingResolvent

/-- Every nonzero scalar is in the resolvent of an actual nilpotent element. -/
theorem nilpotent_resolvent {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (N : A) (n : ℕ) (hn : N ^ n = 0) (z : ℂ) (hz : z ≠ 0) :
    z ∈ resolventSet ℂ N := by
  have hq : IsNilpotent (z⁻¹ • N) := ⟨n, by simp only [smul_pow, hn, smul_zero]⟩
  have scalarUnit : IsUnit (algebraMap ℂ A z) :=
    (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ A)
  have product := scalarUnit.mul hq.isUnit_one_sub
  change IsUnit (algebraMap ℂ A z - N)
  convert product using 1
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_sub,
    smul_smul, mul_inv_cancel₀ hz, one_smul]

/-- A nilpotent block plus an invertible Banach block has meromorphic
actual resolvent at zero. -/
theorem blocks_meromorphicAt_zero {K V : Type*}
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (N : K →L[ℂ] K) (B : V →L[ℂ] V) (n : ℕ)
    (hN : N ^ n = 0) (hB : IsUnit B) :
    MeromorphicAt (resolvent (N.prodMap B)) (0 : ℂ) := by
  have hzero : (0 : ℂ) ∈ resolventSet ℂ B := by
    simpa only [spectrum.mem_resolventSet_iff, ← spectrum.notMem_iff,
      spectrum.zero_notMem_iff] using hB
  have hBnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ resolventSet ℂ B :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      ((spectrum.isOpen_resolventSet B).mem_nhds hzero)
  have hNnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ resolventSet ℂ N := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact nilpotent_resolvent N n hN z hz
  exact MeromorphicBlockResolvent.meromorphicAt N B 0
    (NilpotentResolvent.meromorphicAt_zero N n hN)
    (AnalyticResolvent.analyticAt B hzero).meromorphicAt (hNnear.and hBnear)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Stable kernel/range topological complements imply the actual resolvent
is meromorphic at zero. No meromorphic Fredholm theorem is assumed. -/
theorem meromorphicAt_zero (S : E →L[ℂ] E) (n : ℕ)
    (hcompl : IsTopCompl (S ^ n).ker (S ^ n).range)
    (hker : (S ^ (n + 1)).ker = (S ^ n).ker)
    (hrange : (S ^ (n + 1)).range = (S ^ n).range) :
    MeromorphicAt (resolvent S) (0 : ℂ) := by
  let K := (S ^ n).ker
  let V := (S ^ n).range
  let : CompleteSpace V := hcompl.isClosed'.isComplete.completeSpace_coe
  obtain ⟨N, B, hN, hB, conjugation⟩ := FittingBlocks.exists_blocks S n hcompl hker hrange
  have block := blocks_meromorphicAt_zero N B n hN hB
  have result := ConjugateResolvent.meromorphicAt
    (K.prodEquivOfIsTopCompl V hcompl) (N.prodMap B) 0 block
  rw [conjugation] at result
  exact result

end LeanShared.MeromorphicFittingResolvent
