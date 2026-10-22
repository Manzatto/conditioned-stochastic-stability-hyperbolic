module
public import LeanShared.Analysis.CompactFrequencyJetBounds
public import LeanShared.Analysis.BoundedFiniteJetFamily
public import LeanShared.Analysis.SupportedFiniteJetSpace
public import LeanShared.Analysis.HolderIncrementContinuity
import Mathlib.Tactic

/-! A genuine jointly smooth symbol, a fixed compact frequency cutoff,
and a bounded physical Holder coefficient field construct a supported
Banach-valued finite-jet family, with uniform constants. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.SupportedSmoothSymbolFamily
variable {V Z:Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

theorem exists_family {X P:Type*} [PseudoMetricSpace X]
    (ψ:V × Z→ℂ) (smoothψ:ContDiff ℝ ∞ ψ)
    {D H a:ℝ} (hD:0≤D) (hH:0≤H) (ha:0<a) (n:ℕ)
    (parameters:P→X→V) (value:∀p x,‖parameters p x‖≤D)
    (holder:∀p x y,‖parameters p x-parameters p y‖≤H*dist x y^a)
    (χ:Z→ℂ) (smoothχ:ContDiff ℝ ∞ χ) (compactχ:HasCompactSupport χ):
    ∃B C:ℝ,0≤B ∧ 0≤C ∧
      ∃q:P→X→ᵇ(SupportedFiniteJetSpace.space (Z:=Z) n (tsupport χ)),
        (∀p x z,(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (q p x).val z=
          χ z*ψ (parameters p x,z)) ∧
        (∀p,‖q p‖≤B) ∧∀p x y,‖q p x-q p y‖≤C*dist x y^a:=by
  obtain ⟨B,L,hB,hL,bound,lip⟩:=CompactFrequencyJetBounds.exists_bounds ψ smoothψ χ smoothχ compactχ hD n
  have family (p:P):∃q:X→(BoundedFiniteJetSpace.construct (E:=Z) n (F:=ℂ)).carrier,
      (∀x z,(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (q x) z=χ z*ψ (parameters p x,z)) ∧
      (∀x,‖q x‖≤B) ∧∀x y,‖q x-q y‖≤(L*H)*dist x y^a:=by
    apply BoundedFiniteJetSpace.lift_family n (fun x z=>χ z*ψ (parameters p x,z))
      (fun x=>smoothχ.mul (smoothψ.comp (contDiff_const.prodMk contDiff_id)))
      (fun _=>compactχ.mul_right) hB (mul_nonneg hL hH)
      (fun x j hj z=>bound _ (value p x) j hj z)
    intro x y j hj z
    exact (lip _ _ (value p x) (value p y) j hj z).trans
      ((mul_le_mul_of_nonneg_left (holder p x y) hL).trans_eq (mul_assoc _ _ _).symm)
  choose q physical norms increments using family
  let qs:P→X→SupportedFiniteJetSpace.space n (tsupport χ):=fun p x=>⟨q p x,by
    intro z hz
    rw [physical p x z,image_eq_zero_of_notMem_tsupport hz,zero_mul]⟩
  have qsBound (p:P) (x:X):‖qs p x‖≤B:=norms p x
  have qsHolder (p:P) (x y:X):‖qs p x-qs p y‖≤(L*H)*dist x y^a:=increments p x y
  let result:P→X→ᵇ(SupportedFiniteJetSpace.space n (tsupport χ)):=fun p=>
    BoundedContinuousFunction.ofNormedAddCommGroup (qs p)
      (HolderIncrementContinuity.continuous ha (qsHolder p)) B (qsBound p)
  exact ⟨B,L*H,hB,mul_nonneg hL hH,result,physical,
    (fun p=>(BoundedContinuousFunction.norm_le hB).mpr (qsBound p)),qsHolder⟩
end LeanShared.SupportedSmoothSymbolFamily
