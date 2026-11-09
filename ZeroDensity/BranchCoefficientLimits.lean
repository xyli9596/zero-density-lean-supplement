import ZeroDensity.MainTheorem
import ZeroDensity.PhaseInverse
import ZeroDensity.NormalizedCoefficientLimits
import Mathlib.Analysis.Analytic.Polynomial

/-! Actual transformed coefficients on the inverse branch in Theorem 3.1.
Analyticity is derived from the primitive and branch definitions. Uniform
limits are proved from the actual coefficient data and the inverse-strip
properties. The closed-subsector theorem below now discharges those properties
from the actual primitive and actual inverse branch.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators
namespace ZeroDensity.BranchCoefficientLimits
open Statement MaximalCoefficientData MainTheorem
variable {n : ℕ}

theorem equation_coefficient_analytic (E : EquationData n) (j : Fin n) (z : ℂ) :
    AnalyticAt ℂ (E.coefficient j) z := by
  unfold EquationData.coefficient
  apply Finset.analyticAt_fun_sum
  intro μ _
  have hp : AnalyticAt ℂ (fun x => (E.multipliers j μ).eval x) z :=
    (AnalyticOnNhd.eval_polynomial (E.multipliers j μ)) z (mem_univ z)
  exact hp.mul
    ((analyticAt_const.mul analyticAt_id).cexp)

theorem normalized_coefficient_analytic (E : EquationData n) (S : Selection E)
    (j : Fin n) (z : ℂ) :
    AnalyticAt ℂ (ScaledEquation.normalizedCoefficient E S.ω j) z := by
  have hd : AnalyticAt ℂ (fun t : ℂ => t / S.ω) z := analyticAt_id.div_const
  change AnalyticAt ℂ (fun t => E.coefficient j (t / S.ω) / S.ω ^ (n - j.val)) z
  have hc := AnalyticAt.comp (f := fun t : ℂ => t / S.ω) (x := z)
    (equation_coefficient_analytic E j (z / S.ω)) hd
  exact hc.div_const

theorem actualB_analytic (E : EquationData n) (S : Selection E) (j : ℕ) (z : ℂ) :
    AnalyticAt ℂ (NormalizedCoefficientLimits.actualB E S j) z := by
  change AnalyticAt ℂ (fun t => if h : j < n then
    ScaledEquation.normalizedCoefficient E S.ω ⟨j, h⟩ t else 0) z
  by_cases hj : j < n
  · simpa only [dif_pos hj] using
      normalized_coefficient_analytic E S ⟨j, hj⟩ z
  · simp only [dif_neg hj]
    exact analyticAt_const

theorem primitive_analytic {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ β C) : AnalyticOnNhd ℂ Φ rightHalfPlane := by
  have hd : DifferentiableOn ℂ Φ rightHalfPlane :=
    fun z hz => (hΦ.2 z hz).differentiableAt.differentiableWithinAt
  apply hd.analyticOnNhd
  exact isOpen_lt continuous_const Complex.continuous_re

def branchCoefficient (E : EquationData n) (S : Selection E) (Φ : ℂ → ℂ)
    (B : InverseBranch Φ) (k : Fin n) (s : ℂ) : ℂ :=
  ExactChange.phaseCoeff n (NormalizedCoefficientLimits.actualB E S) Φ k.val (B.ψ s)

theorem phase_coefficient_analytic (E : EquationData n) (S : Selection E)
    {Φ : ℂ → ℂ} {C : ℂ} (hΦ : IsPhasePrimitive Φ (beta E S : ℝ) C)
    (k : Fin n) {z : ℂ} (hz : z ∈ rightHalfPlane) :
    AnalyticAt ℂ (ExactChange.phaseCoeff n
      (NormalizedCoefficientLimits.actualB E S) Φ k.val) z := by
  have hp := primitive_analytic hΦ z hz
  have hq := hp.deriv
  have hnz : deriv Φ z ≠ 0 := by
    rw [(hΦ.2 z hz).deriv]
    exact Complex.exp_ne_zero _
  have hsum : AnalyticAt ℂ (fun t => ∑ j ∈ Finset.range n,
      NormalizedCoefficientLimits.actualB E S j t *
        ExactChange.chainCoeff (deriv Φ) j k.val t) z := by
    apply Finset.analyticAt_fun_sum
    intro j _
    exact (actualB_analytic E S j z).mul (ExactChange.chainCoeff_analytic hq j k.val)
  exact ((ExactChange.chainCoeff_analytic hq n k.val).add hsum).div
    (hq.pow n) (pow_ne_zero n hnz)

theorem branch_coefficient_analytic (E : EquationData n) (S : Selection E)
    {Φ : ℂ → ℂ} {C : ℂ} (hΦ : IsPhasePrimitive Φ (beta E S : ℝ) C)
    (B : InverseBranch Φ) (k : Fin n) :
    AnalyticOnNhd ℂ (branchCoefficient E S Φ B k)
      (CountGeometry.angularSector B.S₀ B.left B.right) := by
  intro s hs
  exact (phase_coefficient_analytic E S hΦ k (B.image_right hs)).comp (B.analytic s hs)

/-- Full transformed-coefficient limit on the actual inverse branch. The
remaining inverse asymptotic is isolated in two elementary strip properties,
rather than assuming a desired coefficient-limit conclusion. -/
theorem branch_coefficient_uniform (E : EquationData n) (S : Selection E)
    {Φ : ℂ → ℂ} {C : ℂ} (hΦ : IsPhasePrimitive Φ (beta E S : ℝ) C)
    (B : InverseBranch Φ) (k : Fin n) (D : Set ℝ)
    (hre : ∀ A : ℝ, ∀ᶠ R : ℝ in atTop, ∀ θ ∈ D,
      A ≤ (B.ψ ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).re)
    {M : ℝ} (hM : 0 ≤ M)
    (him : ∀ᶠ R : ℝ in atTop, ∀ θ ∈ D,
      |(B.ψ ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).im| ≤ M) :
    TendstoUniformlyOn (fun (R θ : ℝ) => branchCoefficient E S Φ B k
      ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      (fun _ => characteristicCoefficient E S k) atTop D := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hd : ∀ z : ℂ, 0 < z.re → deriv Φ z =
      PhaseDerivativeBounds.phaseDerivative ((beta E S : ℝ) : ℂ) z :=
    fun z hz => (hΦ.2 z hz).deriv
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    (NormalizedCoefficientLimits.phaseCoefficient_actual_uniform_epsilon E S Φ hd k hM hε)
  filter_upwards [hre A, him] with R hr hi
  intro θ hθ
  let t := B.ψ ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
  have he := hA t.re (hr θ hθ) t.im (hi θ hθ)
  have ht : (t.re : ℂ) + (t.im : ℂ) * Complex.I = t := by
    apply Complex.ext <;> simp
  rw [ht] at he
  rw [dist_comm, dist_eq_norm]
  exact he

/-- The closed-subsector coefficient limit from actual equation data,
primitive and inverse branch, with no inverse-strip or inverse-asymptotic
hypotheses left for the caller to supply. -/
theorem branch_coefficient_actual_uniform (E : EquationData n) (S : Selection E)
    {Φ : ℂ → ℂ} {C : ℂ} (hΦ : IsPhasePrimitive Φ (beta E S : ℝ) C)
    (B : InverseBranch Φ) (k : Fin n) {a b : ℝ}
    (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    TendstoUniformlyOn (fun (R θ : ℝ) => branchCoefficient E S Φ B k
      ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)))
      (fun _ => characteristicCoefficient E S k) atTop (Icc a b) := by
  obtain ⟨M,him⟩ := PhaseInverse.inverse_imaginary_bounded
    (beta_real_nonneg E S) hΦ B hleft hab hright
  have hre := PhaseInverse.inverse_real_escape
    (beta_real_nonneg E S) hΦ B hleft hab hright
  apply branch_coefficient_uniform E S hΦ B k (Icc a b) ?_
    (show 0 ≤ max 0 M from le_max_left _ _) ?_
  · intro A
    have h := hre.eventually_ge_atTop A
    rwa [eventually_prod_principal_iff] at h
  · filter_upwards [him] with R hR
    intro θ hθ
    exact (hR θ hθ).trans (le_max_right _ _)

#print axioms branch_coefficient_actual_uniform
#print axioms equation_coefficient_analytic
#print axioms branch_coefficient_analytic
#print axioms branch_coefficient_uniform
end ZeroDensity.BranchCoefficientLimits
