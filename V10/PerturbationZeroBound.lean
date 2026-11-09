import V10.PerturbationWeight
import V10.GenericCoefficientZeroBound

/-! The uniform integral zero bound in the proof of Theorem 1.5, derived
from the actual strict exponential-type hypotheses. The actual solution
and its divisor are used; no zero-count bound is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric Asymptotics
open scoped Topology
namespace V10.PerturbationZeroBound
open ZeroDensity.Statement ZeroDensity.CoefficientData
open CoefficientIntegralZeroBound ExponentialType ExponentialScales

/-- Strict type gaps give a single modified weight, a solution-independent
zero-bound constant, and actual negligible added disk mass. The coefficient
family is indexed by all lower derivatives: in the reduced equation the
last perturbation is the zero function. -/
theorem perturbed_integral_zero_bound {n : ℕ} (E : EquationData n)
    {R : Fin n → ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hR : ∀ j, AnalyticOnNhd ℂ (R j) univ)
    (ht : ∀ j, typeOneSphere (R j) < (((gap j : ℝ) * a : ℝ) : EReal)) :
    ∃ b C : ℝ, 0 < b ∧ b < a ∧ 0 < C ∧
      (∀ f : ℂ → ℂ, Differentiable ℂ f →
        (∀ z, iteratedDeriv n f z + ∑ j : Fin n,
          (E.coefficient j z + R j z) * iteratedDeriv j.val f z = 0) →
        (∃ z, f z ≠ 0) →
        (∀ c : ℂ, zeroCount f (closedBall c 1) ≤ C * PerturbationWeight.weight E b c) ∧
        (∀ A : Set ℂ, Bornology.IsBounded A →
          zeroCount f A ≤ C * ∫ z in cthickening 1 A, PerturbationWeight.weight E b z)) ∧
      (∀ d : ℝ, 0 ≤ d → ∀ β : ℝ,
        (fun r : ℝ => ∫ z : ℂ in closedBall 0 (r + d), Real.exp (b * ‖z‖))
          =o[atTop] globalScale a β) := by
  have hn : 0 < n := lt_of_lt_of_le (by norm_num : 0 < 2) E.order_ge_two
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨b, C₀, hb, hba, hC₀, hgrowth⟩ := PerturbationGrowth.finite_family_growth ha hR
    (fun j => by exact_mod_cast gap_pos j) ht
  let B := CoefficientWeight.localConstant E + C₀ * Real.exp (5 * n * b)
  have hB : 0 ≤ B := add_nonneg (CoefficientWeight.localConstant_pos E).le
    (mul_nonneg hC₀.le (Real.exp_nonneg _))
  have hc : Continuous (fun z => fun j : Fin n => E.coefficient j z + R j z) := by
    apply continuous_pi
    intro j
    apply Continuous.add
    · exact continuous_iff_continuousAt.mpr fun z =>
        (ZeroDensity.BranchCoefficientLimits.equation_coefficient_analytic E j z).continuousAt
    · exact (Complex.analyticOnNhd_univ_iff_differentiable.mp (hR j)).continuous
  obtain ⟨C, hC, hzero⟩ := GenericCoefficientZeroBound.exists_uniform_zero_bounds hn hc
    (PerturbationWeight.weight_continuous E b) (PerturbationWeight.weight_ge_one E b) hB
    (fun _ _ hw j => PerturbationWeight.coefficient_local_bound E hb hC₀ hgrowth j hw)
  exact ⟨b, C, hb, hba, hC, hzero,
    fun d hd β => PerturbationWeight.disk_mass_littleO ha hb.le hba hd β⟩

#print axioms perturbed_integral_zero_bound
end V10.PerturbationZeroBound
