import ZeroDensity.InverseBranchFoundations
import ZeroDensity.PhaseDerivativeBounds

/-! Exact integration-by-parts recurrence for actual phase primitives, derived
from their derivatives on the right half-plane. It is not an asymptotic input.
The global beta > 0 remainder estimate is supplied in
`PhasePrimitiveRemainder.lean`; the recurrence itself is exact. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.PrimitiveIntegrationByParts
open ZeroDensity.MainTheorem ZeroDensity.InverseBranchFoundations

theorem phase_shift (β : ℝ) {t : ℂ} (ht : t ≠ 0) :
    phaseDerivative (β-1) t*t = phaseDerivative β t := by
  unfold phaseDerivative
  calc
    _ = Complex.exp (((β-1:ℝ):ℂ)*Complex.log t+t)*Complex.exp (Complex.log t) := by rw [Complex.exp_log ht]
    _ = Complex.exp ((((β-1:ℝ):ℂ)*Complex.log t+t)+Complex.log t) := (Complex.exp_add _ _).symm
    _ = _ := by congr 1; push_cast; ring

theorem phase_hasDeriv (β : ℝ) {t : ℂ} (ht : t ∈ rightHalfPlane) :
    HasDerivAt (phaseDerivative β)
      (phaseDerivative β t+(β:ℂ)*phaseDerivative (β-1) t) t := by
  have hslit : t ∈ Complex.slitPlane := Or.inl ht
  have htn : t ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hh := ZeroDensity.PhaseDerivativeBounds.phaseDerivative_hasDeriv (β:ℂ) hslit
  change HasDerivAt (phaseDerivative β) (phaseDerivative β t*(1+(β:ℂ)*t⁻¹)) t at hh
  convert hh using 1
  have hs := phase_shift β htn
  have hq : phaseDerivative (β-1) t = phaseDerivative β t*t⁻¹ := by
    calc
      _ = (phaseDerivative (β-1) t*t)*t⁻¹ := by rw [mul_assoc,mul_inv_cancel₀ htn,mul_one]
      _ = _ := by rw [hs]
  rw [hq]
  ring

/-- One integration by parts, including every integration constant, is an
exact equality on the whole right half-plane. -/
theorem primitive_recurrence {Φ Ψ : ℂ → ℂ} {β : ℝ} {C D : ℂ}
    (hΦ : IsPhasePrimitive Φ β C) (hΨ : IsPhasePrimitive Ψ (β-1) D) :
    ∀ t ∈ rightHalfPlane,
      Φ t = (phaseDerivative β t-(β:ℂ)*Ψ t)+C-
        (phaseDerivative β 1-(β:ℂ)*D) := by
  let G : ℂ → ℂ := fun t => phaseDerivative β t-(β:ℂ)*Ψ t
  have hg (t : ℂ) (ht : t ∈ rightHalfPlane) : HasDerivAt G (phaseDerivative β t) t := by
    have hh := (phase_hasDeriv β ht).sub ((hΨ.2 t ht).const_mul (β:ℂ))
    convert hh using 1 <;> first | rfl | ring
  let F : ℂ → ℂ := fun t => G t+C-G 1
  have hf (t : ℂ) (ht : t ∈ rightHalfPlane) : HasDerivAt F (phaseDerivative β t) t :=
    ((hg t ht).add_const C).sub_const (G 1)
  have he : EqOn Φ F rightHalfPlane := rightHalfPlane_open.eqOn_of_deriv_eq
    rightHalfPlane_preconnected
    (fun t ht => (hΦ.2 t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hΦ.2 t ht).deriv,(hf t ht).deriv])
    (show (1:ℂ) ∈ rightHalfPlane by norm_num [rightHalfPlane])
    (by simp [F,hΦ.1])
  intro t ht
  simpa [F,G,hΨ.1] using he ht

#print axioms phase_shift
#print axioms phase_hasDeriv
#print axioms primitive_recurrence
end ZeroDensity.PrimitiveIntegrationByParts
