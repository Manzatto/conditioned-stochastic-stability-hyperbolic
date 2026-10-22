module
public import LeanShared.Analysis.NormalizedNonstationarySymbolFamily
public import LeanShared.Analysis.CompactHolderAmplitude
import Mathlib.Tactic

/-! The actual reciprocal-gradient coefficient times the original
physical amplitude is a compactly supported compatible frequency jet.
Its bounds are uniform over the original parameters and dyadic ratios. -/
public noncomputable section
open Set
open scoped ContDiff BoundedContinuousFunction
namespace LeanShared.NormalizedNonstationaryAmplitudeJets
variable {E Z:Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z]

theorem exists_family {P:Type*} {δ D H a G₀ G₁:ℝ}
    (positive:0<δ) (hD:0≤D) (hH:0≤H) (ha:0<a) (hG₀:0≤G₀) (hG₁:0≤G₁)
    (v:E) (n:ℕ) (decode:Z→L[ℝ](E × E))
    (A:P→E→E→L[ℝ]E) (value:∀p x,‖A p x‖≤D)
    (holder:∀p x y,‖A p x-A p y‖≤H*dist x y^a)
    (s t:P→ℝ) (hs:∀p,‖s p‖≤1) (ht:∀p,‖t p‖≤1)
    (χ:Z→ℂ) (smoothχ:ContDiff ℝ ∞ χ) (compactχ:HasCompactSupport χ)
    (g:P→E→ᵇℂ) (compactg:∀p,HasCompactSupport (fun w=>g p w))
    (gvalue:∀p w,‖g p w‖≤G₀)
    (gholder:∀p x y,‖g p x-g p y‖≤G₁*dist x y^a):
    ∃B C:ℝ,0≤B ∧0≤C ∧
      ∃q:P→E→ᵇ(SupportedFiniteJetSpace.space (Z:=Z) n (tsupport χ)),
        (∀p x z,(BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (q p x).val z=
          χ z*g p x*(SmoothNonstationarySymbol.coefficient positive v
            (A p x,(s p • (decode z).1,t p • (decode z).2)):ℂ)) ∧
        (∀p,HasCompactSupport (fun x=>q p x)) ∧
        (∀p x,‖q p x‖≤B) ∧∀p x y,‖q p x-q p y‖≤C*dist x y^a:=by
  obtain ⟨B,C,hB,hC,q,physical,bound,increments⟩:=
    NormalizedNonstationarySymbolFamily.exists_family positive hD hH ha v n decode
      A value holder s t hs ht χ smoothχ compactχ
  have amp (p:P):∃f:E→ᵇ(SupportedFiniteJetSpace.space (Z:=Z) n (tsupport χ)),
      (∀x,f x=g p x • q p x) ∧HasCompactSupport (fun x=>f x) ∧
      (∀x,‖f x‖≤G₀*B) ∧∀x y,‖f x-f y‖≤(G₀*C+G₁*B)*dist x y^a:=by
    simpa only [dist_eq_norm] using CompactHolderAmplitude.exists_amplitude
      (fun x=>g p x) (g p).continuous (compactg p) (q p) hG₀ hG₁ (gvalue p)
      (fun x y=>by simpa only [dist_eq_norm] using gholder p x y)
      (fun x=>((q p).norm_coe_le_norm x).trans (bound p))
      (fun x y=>by simpa only [dist_eq_norm] using increments p x y)
  choose f formula compact norms holder using amp
  refine ⟨G₀*B,G₀*C+G₁*B,mul_nonneg hG₀ hB,by positivity,f,?_,compact,norms,holder⟩
  intro p x z
  rw [formula]
  change (BoundedFiniteJetSpace.construct n (F:=ℂ)).physical (g p x • (q p x).val) z=_
  rw [map_smul,BoundedContinuousFunction.smul_apply,smul_eq_mul,physical]
  ring
end LeanShared.NormalizedNonstationaryAmplitudeJets
