import ZeroDensity.Statement
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The initial linear change t=ωz, with the actual original equation.
This precedes the nonlinear phase change in ExactChange. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace ZeroDensity.ScaledEquation
open Statement

def scaledSolution (f : ℂ → ℂ) (ω : ℂ) (t : ℂ) : ℂ := f (t / ω)

def normalizedCoefficient {n : ℕ} (E : EquationData n) (ω : ℂ)
    (j : Fin n) (t : ℂ) : ℂ :=
  E.coefficient j (t / ω) / ω ^ (n - j.val)

theorem scaled_derivative (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (ω : ℂ) (m : ℕ) (t : ℂ) :
    iteratedDeriv m (scaledSolution f ω) t =
      ω⁻¹ ^ m * iteratedDeriv m f (t / ω) := by
  change iteratedDeriv m (fun x => f (x / ω)) t = _
  have ht := congrFun (iteratedDeriv_comp_const_mul (hf.contDiff (n := m)) ω⁻¹) t
  simpa [scaledSolution, div_eq_mul_inv, mul_comm] using ht

/-- Division by ω^n yields exactly the manuscript's normalized equation. -/
theorem normalized_equation {n : ℕ} (E : EquationData n) {f : ℂ → ℂ}
    (hf : IsSolution E f) (ω : ℂ) (hω : ω ≠ 0) (t : ℂ) :
    iteratedDeriv n (scaledSolution f ω) t +
      ∑ j : Fin n, normalizedCoefficient E ω j t *
        iteratedDeriv j.val (scaledSolution f ω) t = 0 := by
  have he := congrArg (fun v : ℂ => v / ω ^ n) (hf.2 (t / ω))
  simp only [zero_div, add_div, Finset.sum_div] at he
  rw [scaled_derivative f hf.1]
  simp_rw [scaled_derivative f hf.1]
  have hpow (j : Fin n) : ω ^ n = ω ^ (n - j.val) * ω ^ j.val := by
    rw [← pow_add, Nat.sub_add_cancel j.isLt.le]
  have hlead : ω⁻¹ ^ n * iteratedDeriv n f (t / ω) =
      iteratedDeriv n f (t / ω) / ω ^ n := by
    rw [inv_pow]
    ring
  rw [hlead]
  have hsum : (∑ j : Fin n, normalizedCoefficient E ω j t *
      (ω⁻¹ ^ j.val * iteratedDeriv j.val f (t / ω))) =
      ∑ j : Fin n, (E.coefficient j (t / ω) * iteratedDeriv j.val f (t / ω)) /
        ω ^ n := by
    apply Finset.sum_congr rfl
    intro j _
    rw [normalizedCoefficient, hpow j, inv_pow]
    field_simp
  rw [hsum]
  exact he

#print axioms scaled_derivative
#print axioms normalized_equation
end ZeroDensity.ScaledEquation
