import ZeroDensity.CoefficientData

/-! Coefficient construction for any fixed maximal-modulus frequency, including
all possible ties. The maximality specification is precisely the manuscript's
choice condition, not an analytic conclusion. -/
noncomputable section
namespace ZeroDensity.MaximalCoefficientData
open Statement Polynomial
open scoped BigOperators
open CoefficientData (gap gap_pos gap_complex_ne_zero weightedFrequencies mem_weightedFrequencies)
variable {n : ℕ}

structure Selection (E : EquationData n) where
  ω : ℂ
  spec : ω ∈ weightedFrequencies E ∧ ω ≠ 0 ∧
    ∀ q ∈ weightedFrequencies E, ‖q‖ ≤ ‖ω‖

/-- The canonical construction is one instance of the arbitrary choice interface. -/
def canonicalSelection (E : EquationData n) : Selection E :=
  ⟨CoefficientData.omega E, CoefficientData.omega_spec E⟩

def selectedRows (E : EquationData n) (S : Selection E) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j => (gap j : ℂ) * S.ω ∈ E.frequencies j
lemma mem_selectedRows (E : EquationData n) (S : Selection E) (j : Fin n) :
    j ∈ selectedRows E S ↔ (gap j : ℂ) * S.ω ∈ E.frequencies j := by
  classical
  simp [selectedRows]
lemma selectedRows_nonempty (E : EquationData n) (S : Selection E) : (selectedRows E S).Nonempty := by
  obtain ⟨j, μ, hμ, he⟩ := (mem_weightedFrequencies E _).mp (S.spec).1
  refine ⟨j, (mem_selectedRows E S j).mpr ?_⟩
  have hh : μ = (gap j : ℂ) * S.ω := by
    rw [div_eq_iff (gap_complex_ne_zero j)] at he
    simpa [mul_comm] using he
  rwa [← hh]
lemma selectedPolynomial_ne_zero (E : EquationData n) (S : Selection E) {j : Fin n}
    (hj : j ∈ selectedRows E S) : E.multipliers j ((gap j : ℂ) * S.ω) ≠ 0 :=
  E.multiplier_nonzero j _ ((mem_selectedRows E S j).mp hj)

def selectedPolynomial (E : EquationData n) (S : Selection E) (j : Fin n) : Polynomial ℂ :=
  E.multipliers j ((gap j : ℂ) * S.ω)
def multiplierDegree (E : EquationData n) (S : Selection E) (j : Fin n) : ℕ :=
  (selectedPolynomial E S j).natDegree
def degreeRatio (E : EquationData n) (S : Selection E) (j : Fin n) : ℚ :=
  (multiplierDegree E S j : ℚ) / (gap j : ℚ)
lemma exists_maximal_degreeRatio (E : EquationData n) (S : Selection E) :
    ∃ j ∈ selectedRows E S, ∀ k ∈ selectedRows E S, degreeRatio E S k ≤ degreeRatio E S j :=
  (selectedRows E S).exists_max_image (degreeRatio E S) (selectedRows_nonempty E S)
def topRow (E : EquationData n) (S : Selection E) : Fin n := (exists_maximal_degreeRatio E S).choose
def beta (E : EquationData n) (S : Selection E) : ℚ := degreeRatio E S (topRow E S)
lemma topRow_spec (E : EquationData n) (S : Selection E) : topRow E S ∈ selectedRows E S ∧
    ∀ j ∈ selectedRows E S, degreeRatio E S j ≤ beta E S :=
  (exists_maximal_degreeRatio E S).choose_spec
lemma beta_nonneg (E : EquationData n) (S : Selection E) : 0 ≤ beta E S :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
lemma degree_bound (E : EquationData n) (S : Selection E) {j : Fin n} (hj : j ∈ selectedRows E S) :
    (multiplierDegree E S j : ℚ) ≤ beta E S * (gap j : ℚ) := by
  have hp : (0 : ℚ) < gap j := by exact_mod_cast gap_pos j
  exact (div_le_iff₀ hp).mp ((topRow_spec E S).2 j hj)
def attainingRows (E : EquationData n) (S : Selection E) : Finset (Fin n) := by
  classical
  exact (selectedRows E S).filter fun j => degreeRatio E S j = beta E S
lemma attainingRows_nonempty (E : EquationData n) (S : Selection E) : (attainingRows E S).Nonempty := by
  classical
  refine ⟨topRow E S, ?_⟩
  exact Finset.mem_filter.mpr ⟨(topRow_spec E S).1, rfl⟩
lemma normalized_frequency_norm_le (E : EquationData n) (S : Selection E) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) : ‖μ / S.ω‖ ≤ (gap j : ℝ) := by
  have hm := (S.spec).2.2 (μ / (gap j : ℂ))
    ((mem_weightedFrequencies E _).mpr ⟨j, μ, hμ, rfl⟩)
  have hg : (0 : ℝ) < gap j := by exact_mod_cast gap_pos j
  have ho : 0 < ‖S.ω‖ := norm_pos_iff.mpr (S.spec).2.1
  rw [norm_div] at hm ⊢
  have hcast : ‖(gap j : ℂ)‖ = (gap j : ℝ) := by simp
  rw [hcast] at hm
  apply (div_le_iff₀ ho).mpr
  have hh := (div_le_iff₀ hg).mp hm
  simpa [mul_comm] using hh

lemma normalized_frequency_re_le (E : EquationData n) (S : Selection E) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) : (μ / S.ω).re ≤ (gap j : ℝ) :=
  (Complex.re_le_norm _).trans (normalized_frequency_norm_le E S j hμ)

lemma normalized_frequency_re_eq_iff (E : EquationData n) (S : Selection E) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) :
    (μ / S.ω).re = (gap j : ℝ) ↔ μ = (gap j : ℂ) * S.ω := by
  constructor
  · intro he
    have hm := normalized_frequency_norm_le E S j hμ
    have hg : (0 : ℝ) < gap j := by exact_mod_cast gap_pos j
    have hr : |(μ / S.ω).re| = ‖μ / S.ω‖ := by
      rw [abs_of_pos (he ▸ hg)]
      exact le_antisymm (Complex.re_le_norm _) (he ▸ hm)
    have hi := Complex.abs_re_eq_norm.mp hr
    have hc : μ / S.ω = (gap j : ℂ) := by
      apply Complex.ext
      · simpa using he
      · simpa using hi
    exact (div_eq_iff (S.spec).2.1).mp hc
  · intro he
    rw [he, mul_div_cancel_right₀ _ (S.spec).2.1]
    simp

lemma normalized_frequency_re_lt (E : EquationData n) (S : Selection E) (j : Fin n) {μ : ℂ}
    (hμ : μ ∈ E.frequencies j) (hne : μ ≠ (gap j : ℂ) * S.ω) :
    (μ / S.ω).re < (gap j : ℝ) := by
  exact lt_of_le_of_ne (normalized_frequency_re_le E S j hμ)
    (fun he => hne ((normalized_frequency_re_eq_iff E S j hμ).mp he))

lemma selectedRow_lt_top (E : EquationData n) (S : Selection E) {j : Fin n} (hj : j ∈ selectedRows E S) :
    j.val < n - 1 := by
  have hm := (mem_selectedRows E S j).mp hj
  have hn : j.val ≠ n-1 := by
    intro he
    rw [E.reduced j he] at hm
    simpa using hm
  omega

lemma mem_attainingRows (E : EquationData n) (S : Selection E) (j : Fin n) :
    j ∈ attainingRows E S ↔ j ∈ selectedRows E S ∧ degreeRatio E S j = beta E S := by
  classical
  exact Finset.mem_filter

lemma attaining_degree_eq (E : EquationData n) (S : Selection E) {j : Fin n} (hj : j ∈ attainingRows E S) :
    (multiplierDegree E S j : ℚ) = beta E S * (gap j : ℚ) := by
  have hh := (mem_attainingRows E S j).mp hj
  have hg : (gap j : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt (gap_pos j)
  exact (div_eq_iff hg).mp hh.2

lemma nonattaining_degree_lt (E : EquationData n) (S : Selection E) {j : Fin n}
    (hj : j ∈ selectedRows E S) (hn : j ∉ attainingRows E S) :
    (multiplierDegree E S j : ℚ) < beta E S * (gap j : ℚ) := by
  have hg : (0 : ℚ) < gap j := by exact_mod_cast gap_pos j
  apply (div_lt_iff₀ hg).mp
  apply lt_of_le_of_ne ((topRow_spec E S).2 j hj)
  intro he
  exact hn ((mem_attainingRows E S j).mpr ⟨hj, he⟩)

/-- The leading coefficient from the original z-polynomial, scaled by t=ωz. -/
def scaledLeadingCoefficient (E : EquationData n) (S : Selection E) (j : Fin n) : ℂ :=
  (selectedPolynomial E S j).leadingCoeff *
    S.ω ^ ((j.val : ℤ) - (n : ℤ) - (multiplierDegree E S j : ℤ))

lemma scaledLeadingCoefficient_ne_zero (E : EquationData n) (S : Selection E) {j : Fin n}
    (hj : j ∈ selectedRows E S) : scaledLeadingCoefficient E S j ≠ 0 := by
  apply mul_ne_zero
  · exact Polynomial.leadingCoeff_ne_zero.mpr (selectedPolynomial_ne_zero E S hj)
  · exact zpow_ne_zero _ (S.spec).2.1

/-- Absent and subleading rows contribute zero to the characteristic polynomial. -/
def characteristicCoefficient (E : EquationData n) (S : Selection E) (j : Fin n) : ℂ := by
  classical
  exact if j ∈ attainingRows E S then scaledLeadingCoefficient E S j else 0

/-- The actual coefficient polynomial p of Section 2. -/
def characteristicPolynomial (E : EquationData n) (S : Selection E) : Polynomial ℂ :=
  X ^ n + ∑ j : Fin n, C (characteristicCoefficient E S j) * X ^ j.val

lemma characteristicPolynomial_monic (E : EquationData n) (S : Selection E) :
    (characteristicPolynomial E S).Monic :=
  Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)

lemma characteristicPolynomial_natDegree (E : EquationData n) (S : Selection E) :
    (characteristicPolynomial E S).natDegree = n := by
  unfold characteristicPolynomial
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa only [degree_X_pow] using Polynomial.degree_sum_fin_lt (characteristicCoefficient E S)

lemma beta_real_nonneg (E : EquationData n) (S : Selection E) : (0 : ℝ) ≤ (beta E S : ℝ) := by
  exact_mod_cast beta_nonneg E S

lemma degree_bound_real (E : EquationData n) (S : Selection E) {j : Fin n} (hj : j ∈ selectedRows E S) :
    (multiplierDegree E S j : ℝ) ≤ (beta E S : ℝ) * (gap j : ℝ) := by
  exact_mod_cast degree_bound E S hj

lemma attaining_degree_eq_real (E : EquationData n) (S : Selection E) {j : Fin n}
    (hj : j ∈ attainingRows E S) :
    (multiplierDegree E S j : ℝ) = (beta E S : ℝ) * (gap j : ℝ) := by
  exact_mod_cast attaining_degree_eq E S hj

lemma nonattaining_degree_lt_real (E : EquationData n) (S : Selection E) {j : Fin n}
    (hj : j ∈ selectedRows E S) (hn : j ∉ attainingRows E S) :
    (multiplierDegree E S j : ℝ) < (beta E S : ℝ) * (gap j : ℝ) := by
  exact_mod_cast nonattaining_degree_lt E S hj hn

lemma characteristicPolynomial_eq_attaining_sum (E : EquationData n) (S : Selection E) :
    characteristicPolynomial E S = X ^ n +
      ∑ j ∈ attainingRows E S, C (scaledLeadingCoefficient E S j) * X ^ j.val := by
  classical
  unfold characteristicPolynomial
  congr 1
  calc
    _ = ∑ j ∈ attainingRows E S, C (characteristicCoefficient E S j) * X ^ j.val := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [characteristicCoefficient, hj]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [characteristicCoefficient, hj]

lemma characteristicCoefficient_top_zero (E : EquationData n) (S : Selection E) {j : Fin n}
    (hj : j.val = n-1) : characteristicCoefficient E S j = 0 := by
  classical
  have hn : j ∉ attainingRows E S := by
    intro hh
    have ht := selectedRow_lt_top E S ((mem_attainingRows E S j).mp hh).1
    omega
  simp [characteristicCoefficient, hn]


#print axioms mem_selectedRows
#print axioms selectedRows_nonempty
#print axioms selectedPolynomial_ne_zero
#print axioms exists_maximal_degreeRatio
#print axioms topRow_spec
#print axioms beta_nonneg
#print axioms degree_bound
#print axioms attainingRows_nonempty
#print axioms normalized_frequency_norm_le
#print axioms normalized_frequency_re_le
#print axioms normalized_frequency_re_eq_iff
#print axioms normalized_frequency_re_lt
#print axioms selectedRow_lt_top
#print axioms mem_attainingRows
#print axioms attaining_degree_eq
#print axioms nonattaining_degree_lt
#print axioms scaledLeadingCoefficient_ne_zero
#print axioms characteristicPolynomial_monic
#print axioms characteristicPolynomial_natDegree
#print axioms beta_real_nonneg
#print axioms degree_bound_real
#print axioms attaining_degree_eq_real
#print axioms nonattaining_degree_lt_real
#print axioms characteristicPolynomial_eq_attaining_sum
#print axioms characteristicCoefficient_top_zero
end ZeroDensity.MaximalCoefficientData
