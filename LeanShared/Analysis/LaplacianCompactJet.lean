module
public import LeanShared.Analysis.LaplacianFiniteJet

/-! On a fixed compact test support, the finite Schwartz seminorm of an
actual Laplacian power is bounded by its constructed finite directional jet. -/
public noncomputable section
open Set
open scoped SchwartzMap BoundedContinuousFunction
namespace LeanShared.LaplacianFiniteJet
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

theorem seminorm_bound (b : OrthonormalBasis ι ℝ E) (n m : ℕ)
    (K : Set E) (closed : IsClosed K) (R : ℝ) (nonnegative : 0 ≤ R)
    (radius : ∀ x∈K, ‖x‖ ≤ R) (f : 𝓢(E,ℂ))
    (supported : ∀ x∉K, f x=0) :
    ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n f) ≤
      ((1+R)^m*Fintype.card (Index ι n))*‖SchwartzJetSpace.jetMap K (word b n) f‖ := by
  have supportSubset : tsupport f⊆K := by
    apply closure_minimal _ closed
    intro x nonzero
    by_contra outside
    exact nonzero (supported x outside)
  apply ObliqueSchwartzDecay.seminorm_le _ m (by positivity)
  intro x
  by_cases inside : x∈K
  · have powerBound := jet_bound b n K f ⟨x,inside⟩
    have weight : (1+‖x‖)^m ≤ (1+R)^m :=
      pow_le_pow_left₀ (by positivity) (by linarith [radius x inside]) m
    exact (mul_le_mul weight powerBound (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · have zero : FourierSchwartzLaplacian.power n f x=0 := by
      rw [expansion b n f,sum_apply]
      apply Finset.sum_eq_zero
      intro j _
      apply image_eq_zero_of_notMem_tsupport
      intro member
      exact inside (supportSubset (SchwartzJetSpace.tsupport_wordDerivative_subset _ _ member))
    rw [zero,norm_zero,mul_zero]
    positivity
end LeanShared.LaplacianFiniteJet
