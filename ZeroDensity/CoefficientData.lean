import ZeroDensity.Statement
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

noncomputable section
namespace ZeroDensity.CoefficientData
open Statement Polynomial
open scoped BigOperators
variable {n : ℕ}
def gap (j : Fin n) : ℕ := n - j.val
lemma gap_pos (j : Fin n) : 0 < gap j := Nat.sub_pos_of_lt j.isLt

def weightedFrequencies (E : EquationData n) : Finset ℂ := by
  classical
  exact Finset.univ.biUnion fun j => (E.frequencies j).image fun μ => μ / (gap j : ℂ)
lemma mem_weightedFrequencies (E : EquationData n) (q : ℂ) :
    q ∈ weightedFrequencies E ↔ ∃ j : Fin n, ∃ μ ∈ E.frequencies j,
      μ / (gap j : ℂ) = q := by
  classical
  simp [weightedFrequencies]
lemma gap_complex_ne_zero (j : Fin n) : (gap j : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (gap_pos j))
lemma exists_nonzero_weighted (E : EquationData n) :
    ∃ q ∈ weightedFrequencies E, q ≠ 0 := by
  obtain ⟨j, μ, hμ, hn⟩ := E.nonzero_frequency
  refine ⟨μ / (gap j : ℂ), (mem_weightedFrequencies E _).mpr ⟨j, μ, hμ, rfl⟩,
    div_ne_zero hn (gap_complex_ne_zero j)⟩
lemma exists_maximal_frequency (E : EquationData n) :
    ∃ ω ∈ weightedFrequencies E, ω ≠ 0 ∧
      ∀ q ∈ weightedFrequencies E, ‖q‖ ≤ ‖ω‖ := by
  obtain ⟨q, hq, hn⟩ := exists_nonzero_weighted E
  obtain ⟨ω, hω, hmax⟩ := (weightedFrequencies E).exists_max_image norm ⟨q, hq⟩
  refine ⟨ω, hω, ?_, hmax⟩
  intro hz
  have hm := hmax q hq
  rw [hz, norm_zero] at hm
  exact (norm_pos_iff.mpr hn).not_ge hm

def omega (E : EquationData n) : ℂ := (exists_maximal_frequency E).choose
lemma omega_spec (E : EquationData n) : omega E ∈ weightedFrequencies E ∧
    omega E ≠ 0 ∧ ∀ q ∈ weightedFrequencies E, ‖q‖ ≤ ‖omega E‖ :=
  (exists_maximal_frequency E).choose_spec

def selectedRows (E : EquationData n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => (gap j : ℂ) * omega E ∈ E.frequencies j
lemma mem_selectedRows (E : EquationData n) (j : Fin n) :
    j ∈ selectedRows E ↔ (gap j : ℂ) * omega E ∈ E.frequencies j := by
  classical
  simp [selectedRows]
lemma selectedRows_nonempty (E : EquationData n) : (selectedRows E).Nonempty := by
  obtain ⟨j, μ, hμ, he⟩ := (mem_weightedFrequencies E _).mp (omega_spec E).1
  refine ⟨j, (mem_selectedRows E j).mpr ?_⟩
  have hh : μ = (gap j : ℂ) * omega E := by
    rw [div_eq_iff (gap_complex_ne_zero j)] at he
    simpa [mul_comm] using he
  rwa [← hh]
lemma selectedPolynomial_ne_zero (E : EquationData n) {j : Fin n}
    (hj : j ∈ selectedRows E) : E.multipliers j ((gap j : ℂ) * omega E) ≠ 0 :=
  E.multiplier_nonzero j _ ((mem_selectedRows E j).mp hj)

def selectedPolynomial (E : EquationData n) (j : Fin n) : Polynomial ℂ :=
  E.multipliers j ((gap j : ℂ) * omega E)
def multiplierDegree (E : EquationData n) (j : Fin n) : ℕ :=
  (selectedPolynomial E j).natDegree
def degreeRatio (E : EquationData n) (j : Fin n) : ℚ :=
  (multiplierDegree E j : ℚ) / (gap j : ℚ)
lemma exists_maximal_degreeRatio (E : EquationData n) :
    ∃ j ∈ selectedRows E, ∀ k ∈ selectedRows E, degreeRatio E k ≤ degreeRatio E j :=
  (selectedRows E).exists_max_image (degreeRatio E) (selectedRows_nonempty E)
def topRow (E : EquationData n) : Fin n := (exists_maximal_degreeRatio E).choose
def beta (E : EquationData n) : ℚ := degreeRatio E (topRow E)
lemma topRow_spec (E : EquationData n) : topRow E ∈ selectedRows E ∧
    ∀ j ∈ selectedRows E, degreeRatio E j ≤ beta E :=
  (exists_maximal_degreeRatio E).choose_spec
lemma beta_nonneg (E : EquationData n) : 0 ≤ beta E :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
lemma degree_bound (E : EquationData n) {j : Fin n} (hj : j ∈ selectedRows E) :
    (multiplierDegree E j : ℚ) ≤ beta E * (gap j : ℚ) := by
  have hp : (0 : ℚ) < gap j := by exact_mod_cast gap_pos j
  exact (div_le_iff₀ hp).mp ((topRow_spec E).2 j hj)
def attainingRows (E : EquationData n) : Finset (Fin n) := by
  classical
  exact (selectedRows E).filter fun j => degreeRatio E j = beta E
lemma attainingRows_nonempty (E : EquationData n) : (attainingRows E).Nonempty := by
  classical
  refine ⟨topRow E, ?_⟩
  exact Finset.mem_filter.mpr ⟨(topRow_spec E).1, rfl⟩
lemma normalized_frequency_norm_le (E : EquationData n) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) : ‖μ / omega E‖ ≤ (gap j : ℝ) := by
  have hm := (omega_spec E).2.2 (μ / (gap j : ℂ))
    ((mem_weightedFrequencies E _).mpr ⟨j, μ, hμ, rfl⟩)
  have hg : (0 : ℝ) < gap j := by exact_mod_cast gap_pos j
  have ho : 0 < ‖omega E‖ := norm_pos_iff.mpr (omega_spec E).2.1
  rw [norm_div] at hm ⊢
  have hcast : ‖(gap j : ℂ)‖ = (gap j : ℝ) := by simp
  rw [hcast] at hm
  apply (div_le_iff₀ ho).mpr
  have hh := (div_le_iff₀ hg).mp hm
  simpa [mul_comm] using hh

lemma normalized_frequency_re_le (E : EquationData n) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) : (μ / omega E).re ≤ (gap j : ℝ) :=
  (Complex.re_le_norm _).trans (normalized_frequency_norm_le E j hμ)

lemma normalized_frequency_re_eq_iff (E : EquationData n) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) :
    (μ / omega E).re = (gap j : ℝ) ↔ μ = (gap j : ℂ) * omega E := by
  constructor
  · intro he
    have hm := normalized_frequency_norm_le E j hμ
    have hg : (0 : ℝ) < gap j := by exact_mod_cast gap_pos j
    have hr : |(μ / omega E).re| = ‖μ / omega E‖ := by
      rw [abs_of_pos (he ▸ hg)]
      exact le_antisymm (Complex.re_le_norm _) (he ▸ hm)
    have hi := Complex.abs_re_eq_norm.mp hr
    have hc : μ / omega E = (gap j : ℂ) := by
      apply Complex.ext
      · simpa using he
      · simpa using hi
    exact (div_eq_iff (omega_spec E).2.1).mp hc
  · intro he
    rw [he, mul_div_cancel_right₀ _ (omega_spec E).2.1]
    simp

lemma normalized_frequency_re_lt (E : EquationData n) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) (hne : μ ≠ (gap j : ℂ) * omega E) :
    (μ / omega E).re < (gap j : ℝ) := by
  exact lt_of_le_of_ne (normalized_frequency_re_le E j hμ)
    (fun he => hne ((normalized_frequency_re_eq_iff E j hμ).mp he))

lemma selectedRow_lt_top (E : EquationData n) {j : Fin n} (hj : j ∈ selectedRows E) :
    j.val < n - 1 := by
  have hm := (mem_selectedRows E j).mp hj
  have hn : j.val ≠ n-1 := by
    intro he
    rw [E.reduced j he] at hm
    simpa using hm
  omega

lemma mem_attainingRows (E : EquationData n) (j : Fin n) :
    j ∈ attainingRows E ↔ j ∈ selectedRows E ∧ degreeRatio E j = beta E := by
  classical
  exact Finset.mem_filter

lemma attaining_degree_eq (E : EquationData n) {j : Fin n} (hj : j ∈ attainingRows E) :
    (multiplierDegree E j : ℚ) = beta E * (gap j : ℚ) := by
  have hh := (mem_attainingRows E j).mp hj
  have hg : (gap j : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (gap_pos j)
  exact (div_eq_iff hg).mp hh.2

lemma nonattaining_degree_lt (E : EquationData n) {j : Fin n}
    (hj : j ∈ selectedRows E) (hn : j ∉ attainingRows E) :
    (multiplierDegree E j : ℚ) < beta E * (gap j : ℚ) := by
  have hg : (0 : ℚ) < gap j := by exact_mod_cast gap_pos j
  apply (div_lt_iff₀ hg).mp
  apply lt_of_le_of_ne ((topRow_spec E).2 j hj)
  intro he
  exact hn ((mem_attainingRows E j).mpr ⟨hj, he⟩)

/-- The leading coefficient from the original z-polynomial, scaled by t=ωz. -/
def scaledLeadingCoefficient (E : EquationData n) (j : Fin n) : ℂ :=
  (selectedPolynomial E j).leadingCoeff *
    omega E ^ ((j.val : ℤ) - (n : ℤ) - (multiplierDegree E j : ℤ))

lemma scaledLeadingCoefficient_ne_zero (E : EquationData n) {j : Fin n}
    (hj : j ∈ selectedRows E) : scaledLeadingCoefficient E j ≠ 0 := by
  apply mul_ne_zero
  · exact Polynomial.leadingCoeff_ne_zero.mpr (selectedPolynomial_ne_zero E hj)
  · exact zpow_ne_zero _ (omega_spec E).2.1

/-- Absent and subleading rows contribute zero to the characteristic polynomial. -/
def characteristicCoefficient (E : EquationData n) (j : Fin n) : ℂ := by
  classical
  exact if j ∈ attainingRows E then scaledLeadingCoefficient E j else 0

/-- The actual coefficient polynomial p of Section 2. -/
def characteristicPolynomial (E : EquationData n) : Polynomial ℂ :=
  X ^ n + ∑ j : Fin n, C (characteristicCoefficient E j) * X ^ j.val

lemma characteristicPolynomial_monic (E : EquationData n) :
    (characteristicPolynomial E).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

lemma characteristicPolynomial_natDegree (E : EquationData n) :
    (characteristicPolynomial E).natDegree = n := by
  unfold characteristicPolynomial
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa only [degree_X_pow] using Polynomial.degree_sum_fin_lt (characteristicCoefficient E)

lemma beta_real_nonneg (E : EquationData n) : (0 : ℝ) ≤ (beta E : ℝ) := by
  exact_mod_cast beta_nonneg E

lemma degree_bound_real (E : EquationData n) {j : Fin n} (hj : j ∈ selectedRows E) :
    (multiplierDegree E j : ℝ) ≤ (beta E : ℝ) * (gap j : ℝ) := by
  exact_mod_cast degree_bound E hj

lemma attaining_degree_eq_real (E : EquationData n) {j : Fin n}
    (hj : j ∈ attainingRows E) :
    (multiplierDegree E j : ℝ) = (beta E : ℝ) * (gap j : ℝ) := by
  exact_mod_cast attaining_degree_eq E hj

lemma nonattaining_degree_lt_real (E : EquationData n) {j : Fin n}
    (hj : j ∈ selectedRows E) (hn : j ∉ attainingRows E) :
    (multiplierDegree E j : ℝ) < (beta E : ℝ) * (gap j : ℝ) := by
  exact_mod_cast nonattaining_degree_lt E hj hn

lemma characteristicPolynomial_eq_attaining_sum (E : EquationData n) :
    characteristicPolynomial E = X ^ n +
      ∑ j ∈ attainingRows E, C (scaledLeadingCoefficient E j) * X ^ j.val := by
  classical
  unfold characteristicPolynomial
  congr 1
  calc
    _ = ∑ j ∈ attainingRows E, C (characteristicCoefficient E j) * X ^ j.val := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [characteristicCoefficient, hj]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [characteristicCoefficient, hj]

lemma characteristicCoefficient_top_zero (E : EquationData n) {j : Fin n}
    (hj : j.val = n-1) : characteristicCoefficient E j = 0 := by
  classical
  have hn : j ∉ attainingRows E := by
    intro hh
    have ht := selectedRow_lt_top E ((mem_attainingRows E j).mp hh).1
    omega
  simp [characteristicCoefficient, hn]

#print axioms beta_real_nonneg
#print axioms degree_bound_real
#print axioms attaining_degree_eq_real
#print axioms nonattaining_degree_lt_real
#print axioms characteristicPolynomial_eq_attaining_sum
#print axioms characteristicCoefficient_top_zero
#print axioms exists_maximal_frequency
#print axioms selectedRows_nonempty
#print axioms beta_nonneg
#print axioms degree_bound
#print axioms attainingRows_nonempty
#print axioms normalized_frequency_norm_le
#print axioms normalized_frequency_re_eq_iff
#print axioms normalized_frequency_re_lt
#print axioms selectedRow_lt_top
#print axioms attaining_degree_eq
#print axioms nonattaining_degree_lt
#print axioms scaledLeadingCoefficient_ne_zero
#print axioms characteristicPolynomial_monic
#print axioms characteristicPolynomial_natDegree

end ZeroDensity.CoefficientData
