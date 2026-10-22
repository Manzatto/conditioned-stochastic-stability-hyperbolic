module
public import LeanShared.Analysis.LaplacianCompactJet

/-! One explicit finite jet controls both the test function and its required
Laplacian power on a compact support. -/
public noncomputable section
open Set
open scoped SchwartzMap BoundedContinuousFunction
namespace LeanShared.LaplacianFiniteJet
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]
@[expose] def testWords (b : ι→E) (n : ℕ) : Index ι 0 ⊕ Index ι n → List E :=
  Sum.elim (word b 0) (word b n)

omit [FiniteDimensional ℝ E] in
theorem test_jet_left (b : OrthonormalBasis ι ℝ E) (n : ℕ) (K : Set E) (f : 𝓢(E,ℂ)) :
    ‖SchwartzJetSpace.jetMap K (word b 0) f‖ ≤
      ‖SchwartzJetSpace.jetMap K (testWords b n) f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact norm_le_pi_norm (SchwartzJetSpace.jetMap K (testWords b n) f) (Sum.inl i)

omit [FiniteDimensional ℝ E] in
theorem test_jet_right (b : OrthonormalBasis ι ℝ E) (n : ℕ) (K : Set E) (f : 𝓢(E,ℂ)) :
    ‖SchwartzJetSpace.jetMap K (word b n) f‖ ≤
      ‖SchwartzJetSpace.jetMap K (testWords b n) f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  exact norm_le_pi_norm (SchwartzJetSpace.jetMap K (testWords b n) f) (Sum.inr i)

theorem test_seminorm_bound (b : OrthonormalBasis ι ℝ E) (n m : ℕ)
    (K : Set E) (closed : IsClosed K) (R : ℝ) (nonnegative : 0 ≤ R)
    (radius : ∀ x∈K, ‖x‖ ≤ R) (f : 𝓢(E,ℂ))
    (supported : ∀ x∉K, f x=0) :
    ObliqueSchwartzDecay.seminorm m f+
      ObliqueSchwartzDecay.seminorm m (FourierSchwartzLaplacian.power n f) ≤
      ((1+R)^m*(Fintype.card (Index ι 0)+Fintype.card (Index ι n)))*
        ‖SchwartzJetSpace.jetMap K (testWords b n) f‖ := by
  have left := seminorm_bound b 0 m K closed R nonnegative radius f supported
  change ObliqueSchwartzDecay.seminorm m f ≤ _ at left
  have right := seminorm_bound b n m K closed R nonnegative radius f supported
  have leftCombined := mul_le_mul_of_nonneg_left (test_jet_left b n K f)
    (by positivity : 0 ≤ (1+R)^m*Fintype.card (Index ι 0))
  have rightCombined := mul_le_mul_of_nonneg_left (test_jet_right b n K f)
    (by positivity : 0 ≤ (1+R)^m*Fintype.card (Index ι n))
  exact (add_le_add (left.trans leftCombined) (right.trans rightCombined)).trans_eq (by ring)
end LeanShared.LaplacianFiniteJet
