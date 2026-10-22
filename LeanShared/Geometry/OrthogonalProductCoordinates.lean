module
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Fixed orthogonal factor coordinates in a genuine Hilbert model. The
max-norm product retains its norm; only its axis images are orthogonal. -/
public noncomputable section
namespace LeanShared.OrthogonalProductCoordinates
variable {X Y E : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E]

@[expose] def hilbertEquiv (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) :
    WithLp 2 (X×Y)≃ₗᵢ[ℝ]E :=
  (stdOrthonormalBasis ℝ (WithLp 2 (X×Y))).equiv (stdOrthonormalBasis ℝ E)
    (finCongr (((WithLp.linearEquiv 2 ℝ (X×Y)).finrank_eq).trans dimension))

@[expose] def equiv (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) : (X×Y)≃L[ℝ]E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).symm.trans (hilbertEquiv dimension).toContinuousLinearEquiv

theorem axes_inner (dimension : Module.finrank ℝ (X×Y)=Module.finrank ℝ E) (x : X) (y : Y) :
    inner ℝ (equiv dimension (x,0)) (equiv dimension (0,y))=0 := by
  change inner ℝ (hilbertEquiv dimension (WithLp.toLp 2 (x,0)))
    (hilbertEquiv dimension (WithLp.toLp 2 (0,y)))=0
  rw [(hilbertEquiv dimension).inner_map_map]
  simp

end LeanShared.OrthogonalProductCoordinates
