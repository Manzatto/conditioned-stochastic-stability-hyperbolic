module
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.Complex.Basic

/-! Strongly convergent regularizers recover the trace of every actual
finite-dimensional compression inside an arbitrary normed carrier. The
regularizers themselves need not have finite rank. This supplies the
finite spectral part of a regularized-trace argument; it makes no claim
about the complementary infinite-dimensional trace. -/
public noncomputable section
open Filter
open scoped Topology BigOperators
namespace LeanShared.StrongFiniteSpectralTrace
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem trace_eq_coordinates (A : V →L[ℂ] V) :
    LinearMap.trace ℂ V A.toLinearMap =
      ∑ i, (Module.finBasis ℂ V).coord i (A (Module.finBasis ℂ V i)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  rfl

/-- Strong convergence on the infinite carrier implies ordinary trace
convergence after a fixed finite-dimensional compression. -/
theorem compression_tendsto
    {ι : Type*} {l : Filter ι} (Q : ι → E →L[ℂ] E)
    (strong : ∀ x : E, Tendsto (fun j => Q j x) l (𝓝 x))
    (A : E →L[ℂ] E) (embed : V →L[ℂ] E) (extract : E →L[ℂ] V) :
    Tendsto (fun j => LinearMap.trace ℂ V
      (extract.comp ((Q j).comp (A.comp embed))).toLinearMap) l
      (𝓝 (LinearMap.trace ℂ V (extract.comp (A.comp embed)).toLinearMap)) := by
  classical
  simp_rw [trace_eq_coordinates]
  apply tendsto_finsetSum
  intro i _
  have coordinate := ((Module.finBasis ℂ V).coord i).continuous_of_finiteDimensional
  exact (coordinate.tendsto _).comp
    ((extract.continuous.tendsto _).comp (strong (A (embed (Module.finBasis ℂ V i)))))

/-- The literal compression associated to an actual finite-range operator
on the carrier. For an idempotent this is its spectral range compression. -/
@[expose] def rangeCompression (P A : E →L[ℂ] E) : P.range →L[ℂ] P.range :=
  P.rangeRestrict.comp (A.comp P.range.subtypeL)

theorem rangeCompression_tendsto (P : E →L[ℂ] E)
    [FiniteDimensional ℂ P.range] {ι : Type*} {l : Filter ι}
    (Q : ι → E →L[ℂ] E)
    (strong : ∀ x : E, Tendsto (fun j => Q j x) l (𝓝 x)) (A : E →L[ℂ] E) :
    Tendsto (fun j => LinearMap.trace ℂ P.range
      (rangeCompression P ((Q j).comp A)).toLinearMap) l
      (𝓝 (LinearMap.trace ℂ P.range (rangeCompression P A).toLinearMap)) := by
  exact compression_tendsto Q strong A P.range.subtypeL P.rangeRestrict


/-- A nilpotent part contributes no extra trace to the powers of a single
spectral block, including nontrivial Jordan directions. -/
theorem trace_powers_of_shift_nilpotent (A : Module.End ℂ V) (lam : ℂ)
    (nilpotent : IsNilpotent (A - algebraMap ℂ (Module.End ℂ V) lam)) (n : ℕ) :
    LinearMap.trace ℂ V (A ^ n) = (Module.finrank ℂ V : ℂ) * lam ^ n := by
  induction n with
  | zero => simp only [pow_zero, LinearMap.trace_one, mul_one]
  | succ n ih =>
    have recurrence := LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent
      lam ((Commute.refl A).pow_left n) nilpotent
    change LinearMap.trace ℂ V (A ^ n * A) = _ at recurrence
    rw [pow_succ, recurrence, ih, pow_succ]
    ring

end LeanShared.StrongFiniteSpectralTrace
