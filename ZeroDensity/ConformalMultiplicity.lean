import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.Basic

namespace ZeroDensity.ConformalMultiplicity
open scoped Topology

/-- An analytic change of variable with nonzero derivative preserves zero order. -/
theorem order_comp {f ψ : ℂ → ℂ} {s : ℂ}
    (hf : AnalyticAt ℂ f (ψ s)) (hψ : AnalyticAt ℂ ψ s) (hd : deriv ψ s ≠ 0) :
    analyticOrderAt (f ∘ ψ) s = analyticOrderAt f (ψ s) := by
  rw [hf.analyticOrderAt_comp hψ, hψ.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd]
  simp

/-- Coordinate changes preserve the actual scalar zero equation. -/
theorem zero_comp_iff {f ψ : ℂ → ℂ} {s : ℂ} :
    (f ∘ ψ) s = 0 ↔ f (ψ s) = 0 := Iff.rfl

/-- Pointwise divisor preservation on analytic domains. This states equality of
actual function divisors, not equality of abstract supplied multiplicities. -/
theorem divisor_comp {f ψ : ℂ → ℂ} {U V : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hψ : AnalyticOnNhd ℂ ψ V)
    (hmap : Set.MapsTo ψ V U) {s : ℂ} (hs : s ∈ V) (hd : deriv ψ s ≠ 0) :
    MeromorphicOn.divisor (f ∘ ψ) V s = MeromorphicOn.divisor f U (ψ s) := by
  have hcomp : AnalyticOnNhd ℂ (f ∘ ψ) V := fun z hz =>
    (hf (ψ z) (hmap hz)).comp (hψ z hz)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hcomp hs,
    MeromorphicOn.AnalyticOnNhd.divisor_apply hf (hmap hs), order_comp
    (hf (ψ s) (hmap hs)) (hψ s hs) hd]

end ZeroDensity.ConformalMultiplicity
