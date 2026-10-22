module

public import LeanShared.Analysis.SimpleSquareCompactLeft

/-! Actual rank-one projectors and complementary spectral splitting for a
simple nonzero eigenvalue. The projector is constructed from the proved
left-functional theorem, not supplied as a spectral-calculus source. -/

public noncomputable section
open Module ContinuousLinearMap

namespace LeanShared.SimpleSquareCompactProjection

variable {𝕜 X : Type*} [RCLike 𝕜] [LocallyCompactSpace 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- The resulting ordinary projector data, including exact splitting of all
nonzero complementary spectral points. -/
structure Data (T : X →L[𝕜] X) (μ : 𝕜) (v : X) where
  mean : X →L[𝕜] 𝕜
  normalization : mean v = 1
  left : ∀ x, mean (T x) = μ * mean x
  projection_idempotent : (mean.smulRight v) ^ 2 = mean.smulRight v
  right_action : T * mean.smulRight v = μ • mean.smulRight v
  left_action : mean.smulRight v * T = μ • mean.smulRight v
  generalized_fixed : ∀ n x, ((T - μ • 1 : X →L[𝕜] X) ^ n) x = 0 →
    mean.smulRight v x = x
  remainder_square_compact : IsCompactOperator ((T - μ • mean.smulRight v) ^ 2 : X →L[𝕜] X)
  remainder_spectrum : ∀ z : 𝕜, z ≠ 0 →
    (z ∈ spectrum 𝕜 (T - μ • mean.smulRight v) ↔ z ∈ spectrum 𝕜 T ∧ z ≠ μ)

/-- Construct the projector and its spectral splitting from square compactness
and order-two algebraic simplicity. -/
theorem exists_data (T : X →L[𝕜] X)
    (hT : IsCompactOperator (T ^ 2 : X →L[𝕜] X))
    (μ : 𝕜) (hμ : μ ≠ 0) (v : X) (hv : v ≠ 0) (heig : T v = μ • v)
    (simple : ∀ x : X, ((T - μ • 1 : X →L[𝕜] X) ^ 2) x = 0 → ∃ a : 𝕜, x = a • v) :
    Nonempty (Data T μ v) := by
  obtain ⟨ℓ, hℓv, hleft⟩ := SimpleSquareCompactLeft.exists_left T hT μ hμ v hv heig simple
  let p := ℓ.smulRight v
  let R := T - μ • p
  have hSv : (T - μ • 1 : X →L[𝕜] X) v = 0 := by simp [heig]
  have generalized : ∀ n x, ((T - μ • 1 : X →L[𝕜] X) ^ n) x = 0 →
      ∃ a : 𝕜, x = a • v := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simp only [pow_zero, one_apply_eq_self] at hx
      exact ⟨0, by simp [hx]⟩
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_apply_eq_comp] at hx
      obtain ⟨a, ha⟩ := ih _ hx
      apply simple x
      rw [pow_two, mul_apply_eq_comp, ha, map_smul, hSv, smul_zero]
  have hpcompact : IsCompactOperator (R ^ 2 : X →L[𝕜] X) := by
    have compact := SimpleSquareCompactLeft.square_compact_add_rankOne T hT ((-μ) • ℓ) v
    have he : T + ((-μ) • ℓ).smulRight v = R := by
      ext x
      simp only [R, p, add_apply, sub_apply, smul_apply, smulRight_apply, smul_smul]
      module
    rw [he] at compact
    exact compact
  have hRleft (x : X) : ℓ (R x) = 0 := by
    simp only [R, p, sub_apply, smul_apply, smulRight_apply, map_sub, map_smul,
      hleft, hℓv, smul_eq_mul, mul_one, sub_self]
  have remainder_to_original {z : 𝕜} (hz : z ≠ 0) {x : X}
      (he : R x = z • x) : ℓ x = 0 ∧ T x = z • x := by
    have hh : z * ℓ x = 0 := by rw [← smul_eq_mul, ← map_smul, ← he, hRleft]
    have hzero : ℓ x = 0 := (mul_eq_zero.mp hh).resolve_left hz
    refine ⟨hzero, ?_⟩
    simpa only [R, p, sub_apply, smul_apply, smulRight_apply, hzero, zero_smul,
      smul_zero, sub_zero] using he
  have splitting {z : 𝕜} (hz : z ≠ 0) :
      z ∈ spectrum 𝕜 R ↔ z ∈ spectrum 𝕜 T ∧ z ≠ μ := by
    constructor
    · intro hs
      obtain ⟨x, hx, he⟩ := SquareCompactFredholm.eigenvector_of_mem_spectrum R hpcompact hz hs
      obtain ⟨hℓx, hTx⟩ := remainder_to_original hz he
      have spectrumT : z ∈ spectrum 𝕜 T := by
        rw [ContinuousLinearMap.spectrum_eq]
        exact (Module.End.hasEigenvalue_of_hasEigenvector
          (show Module.End.HasEigenvector (T : Module.End 𝕜 X) z x from
            ⟨Module.End.mem_eigenspace_iff.mpr hTx, hx⟩)).mem_spectrum
      refine ⟨spectrumT, ?_⟩
      intro heq
      rw [heq] at hTx
      have hker : ((T - μ • 1 : X →L[𝕜] X) ^ 2) x = 0 := by
        rw [pow_two, mul_apply_eq_comp]
        have hh : (T - μ • 1 : X →L[𝕜] X) x = 0 := by simp [hTx]
        rw [hh, map_zero]
      obtain ⟨a, rfl⟩ := simple x hker
      have ha : a = 0 := by simpa only [map_smul, hℓv, smul_eq_mul, mul_one] using hℓx
      exact hx (by simp [ha])
    · rintro ⟨hs, hzm⟩
      obtain ⟨x, hx, he⟩ := SquareCompactFredholm.eigenvector_of_mem_spectrum T hT hz hs
      have hℓx : ℓ x = 0 := by
        have hh : (z - μ) * ℓ x = 0 := by
          have hh := congrArg ℓ he
          simp only [hleft, map_smul, smul_eq_mul] at hh
          linear_combination -hh
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hzm)
      have heR : R x = z • x := by
        simp only [R, p, sub_apply, smul_apply, smulRight_apply, hℓx, zero_smul,
          smul_zero, sub_zero, he]
      rw [ContinuousLinearMap.spectrum_eq]
      exact (Module.End.hasEigenvalue_of_hasEigenvector
        (show Module.End.HasEigenvector (R : Module.End 𝕜 X) z x from
          ⟨Module.End.mem_eigenspace_iff.mpr heR, hx⟩)).mem_spectrum
  refine ⟨{
    mean := ℓ
    normalization := hℓv
    left := hleft
    projection_idempotent := ?_
    right_action := ?_
    left_action := ?_
    generalized_fixed := ?_
    remainder_square_compact := hpcompact
    remainder_spectrum := fun z hz => splitting hz }⟩
  · ext x
    simp [pow_two, mul_apply_eq_comp, hℓv]
  · ext x
    simp [heig, smul_smul, mul_comm]
  · ext x
    simp [hleft, smul_smul]
  · intro n x hx
    obtain ⟨a, rfl⟩ := generalized n x hx
    simp [hℓv]

end LeanShared.SimpleSquareCompactProjection
