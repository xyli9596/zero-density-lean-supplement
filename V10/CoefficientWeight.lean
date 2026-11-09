import ZeroDensity.CoefficientData
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Polynomial.Basic

/-!
# The manuscript's actual coefficient weight and its local coefficient bound

The weight is the displayed finite sum of polynomial degrees and exponential
frequencies. Constants are constructed from the actual polynomial coefficients.
The local coefficient estimate is proved on every radius-five neighborhood.
-/
noncomputable section
open Set Metric
open scoped BigOperators
namespace V10.CoefficientWeight
open ZeroDensity.Statement ZeroDensity.CoefficientData

variable {n : ℕ}

def term (E : EquationData n) (j : Fin n) (ξ z : ℂ) : ℝ :=
  (1 + ‖z‖) ^ ((E.multipliers j ξ).natDegree / (gap j : ℝ)) *
    Real.exp ((ξ * z).re / (gap j : ℝ))

def weight (E : EquationData n) (z : ℂ) : ℝ :=
  1 + ∑ j : Fin n, ∑ ξ ∈ E.frequencies j, term E j ξ z

theorem term_nonneg (E : EquationData n) (j : Fin n) (ξ z : ℂ) : 0 ≤ term E j ξ z := by
  unfold term
  positivity

theorem weight_ge_one (E : EquationData n) (z : ℂ) : 1 ≤ weight E z := by
  unfold weight
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun ξ _ => term_nonneg E j ξ z)

theorem term_le_weight (E : EquationData n) (j : Fin n) {ξ : ℂ}
    (hξ : ξ ∈ E.frequencies j) (z : ℂ) : term E j ξ z ≤ weight E z := by
  have hrow : term E j ξ z ≤ ∑ μ ∈ E.frequencies j, term E j μ z :=
    Finset.single_le_sum (fun μ _ => term_nonneg E j μ z) hξ
  have hall : (∑ μ ∈ E.frequencies j, term E j μ z) ≤
      ∑ i : Fin n, ∑ μ ∈ E.frequencies i, term E i μ z :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun μ _ => term_nonneg E i μ z)
      (Finset.mem_univ j)
  exact (hrow.trans hall).trans (by unfold weight; linarith)

theorem term_pow_gap (E : EquationData n) (j : Fin n) (ξ z : ℂ) :
    term E j ξ z ^ gap j =
      (1 + ‖z‖) ^ (E.multipliers j ξ).natDegree * Real.exp ((ξ * z).re) := by
  have hg : (gap j : ℝ) ≠ 0 := by exact_mod_cast (gap_pos j).ne'
  unfold term
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), div_mul_cancel₀ _ hg,
    Real.rpow_natCast, ← Real.exp_nat_mul]
  congr 2
  field_simp

def polynomialMass (P : Polynomial ℂ) : ℝ := ∑ q ∈ P.support, ‖P.coeff q‖

theorem polynomialMass_nonneg (P : Polynomial ℂ) : 0 ≤ polynomialMass P :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Coefficientwise polynomial bound, including constant and zero polynomials. -/
theorem norm_eval_le (P : Polynomial ℂ) (z : ℂ) :
    ‖P.eval z‖ ≤ polynomialMass P * (1 + ‖z‖) ^ P.natDegree := by
  rw [Polynomial.eval_eq_sum]
  change ‖∑ q ∈ P.support, P.coeff q * z ^ q‖ ≤ _
  calc
    _ ≤ ∑ q ∈ P.support, ‖P.coeff q * z ^ q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ P.support, ‖P.coeff q‖ * (1 + ‖z‖) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (norm_nonneg z) (by linarith : ‖z‖ ≤ 1 + ‖z‖) q).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg z] : (1 : ℝ) ≤ 1 + ‖z‖)
          (Polynomial.le_natDegree_of_mem_supp q hq))
    _ = _ := by rw [← Finset.sum_mul]; rfl

def termConstant (P : Polynomial ℂ) (ξ : ℂ) : ℝ :=
  (6 : ℝ) ^ P.natDegree * Real.exp (5 * ‖ξ‖) * polynomialMass P

theorem termConstant_nonneg (P : Polynomial ℂ) (ξ : ℂ) : 0 ≤ termConstant P ξ := by
  unfold termConstant
  exact mul_nonneg (by positivity) (polynomialMass_nonneg P)

/-- The actual polynomial-exponential summand on a five-neighborhood is
bounded by its own contribution to the manuscript weight, raised to the gap. -/
theorem summand_local_bound (E : EquationData n) (j : Fin n) (ξ : ℂ)
    {z w : ℂ} (hw : ‖w - z‖ ≤ 5) :
    ‖(E.multipliers j ξ).eval w * Complex.exp (ξ * w)‖ ≤
      termConstant (E.multipliers j ξ) ξ * term E j ξ z ^ gap j := by
  have hnorm : 1 + ‖w‖ ≤ 6 * (1 + ‖z‖) := by
    have hh := norm_add_le (w - z) z
    rw [sub_add_cancel] at hh
    nlinarith [norm_nonneg z]
  have hre : (ξ * w).re ≤ (ξ * z).re + 5 * ‖ξ‖ := by
    have h := Complex.re_le_norm (ξ * (w - z))
    rw [norm_mul, mul_sub, Complex.sub_re] at h
    have hmul := mul_le_mul_of_nonneg_left hw (norm_nonneg ξ)
    linarith
  rw [norm_mul, Complex.norm_exp, term_pow_gap]
  calc
    _ ≤ (polynomialMass (E.multipliers j ξ) * (6 * (1 + ‖z‖)) ^
        (E.multipliers j ξ).natDegree) * Real.exp ((ξ * z).re + 5 * ‖ξ‖) := by
      apply mul_le_mul _ (Real.exp_le_exp.mpr hre) (Real.exp_nonneg _)
        (mul_nonneg (polynomialMass_nonneg _) (by positivity))
      exact (norm_eval_le (E.multipliers j ξ) w).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm _)
          (polynomialMass_nonneg _))
    _ = _ := by rw [mul_pow, Real.exp_add]; unfold termConstant; ring

def localConstant (E : EquationData n) : ℝ :=
  1 + ∑ j : Fin n, ∑ ξ ∈ E.frequencies j, termConstant (E.multipliers j ξ) ξ

theorem localConstant_pos (E : EquationData n) : 0 < localConstant E := by
  unfold localConstant
  have hh : 0 ≤ ∑ j : Fin n, ∑ ξ ∈ E.frequencies j, termConstant (E.multipliers j ξ) ξ :=
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => termConstant_nonneg _ _
  linarith

/-- The actual coefficient bound with a single constant determined only by
all polynomial coefficients and frequencies of the equation. -/
theorem coefficient_local_bound (E : EquationData n) (j : Fin n)
    {z w : ℂ} (hw : ‖w - z‖ ≤ 5) :
    ‖E.coefficient j w‖ ≤ localConstant E * weight E z ^ gap j := by
  unfold EquationData.coefficient
  calc
    _ ≤ ∑ ξ ∈ E.frequencies j, ‖(E.multipliers j ξ).eval w * Complex.exp (ξ * w)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ξ ∈ E.frequencies j, termConstant (E.multipliers j ξ) ξ * weight E z ^ gap j := by
      apply Finset.sum_le_sum
      intro ξ hξ
      exact (summand_local_bound E j ξ hw).trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (term_nonneg E j ξ z) (term_le_weight E j hξ z) _)
          (termConstant_nonneg _ _))
    _ = (∑ ξ ∈ E.frequencies j, termConstant (E.multipliers j ξ) ξ) * weight E z ^ gap j :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg ((zero_lt_one.trans_le (weight_ge_one E z)).le) _)
      have hh : (∑ ξ ∈ E.frequencies j, termConstant (E.multipliers j ξ) ξ) ≤
          ∑ i : Fin n, ∑ ξ ∈ E.frequencies i, termConstant (E.multipliers i ξ) ξ :=
        Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg fun ξ _ => termConstant_nonneg (E.multipliers i ξ) ξ)
        (Finset.mem_univ j)
      unfold localConstant
      linarith

theorem weight_continuous (E : EquationData n) : Continuous (weight E) := by
  unfold weight
  apply continuous_const.add
  apply continuous_finsetSum
  intro j _
  apply continuous_finsetSum
  intro ξ _
  unfold term
  apply Continuous.mul
  · exact (continuous_const.add continuous_norm).rpow_const
      (fun z => Or.inl (by positivity : 1 + ‖z‖ ≠ 0))
  · fun_prop

#print axioms coefficient_local_bound
#print axioms weight_continuous
end V10.CoefficientWeight
