import ZeroDensity.MaximalCoefficientData
import ZeroDensity.FrequencyDecay
import ZeroDensity.PolynomialLimits
import ZeroDensity.PhaseDerivativeBounds
import ZeroDensity.ScaledEquation

/-! Limits of the actual original coefficient sums after both normalizations.
The maximal frequency is arbitrary, including tied maxima. -/
noncomputable section
namespace ZeroDensity.NormalizedCoefficientLimits
open Filter Set Polynomial
open scoped Topology BigOperators
open Statement MaximalCoefficientData
open CoefficientData (gap gap_pos)

/-- The principal real-power phase derivative. -/
def q (β : ℝ) (t : ℂ) : ℂ := t^(β:ℂ) * Complex.exp t

def stripPoint (y : ℝ → ℝ) (r : ℝ) : ℂ := (r:ℂ)+(y r:ℂ)*Complex.I

lemma stripPoint_re (y : ℝ → ℝ) (r : ℝ) : (stripPoint y r).re = r := by
  simp [stripPoint]

lemma stripPoint_norm_tendsto (y : ℝ → ℝ) :
    Tendsto (fun r : ℝ => ‖stripPoint y r‖) atTop atTop := by
  apply PhaseDerivativeBounds.coordinate_norm_tendsto
  simp_rw [stripPoint_re]
  exact tendsto_id

lemma q_eq_phaseDerivative {t : ℂ} (ht : t ≠ 0) (β : ℝ) :
    q β t = PhaseDerivativeBounds.phaseDerivative (β:ℂ) t := by
  rw [q, Complex.cpow_def_of_ne_zero ht, ← Complex.exp_add]
  simp [PhaseDerivativeBounds.phaseDerivative, mul_comm]

lemma term_cancel (P : Polynomial ℂ) (μ ω t : ℂ) (β : ℝ) (m : ℕ) :
    P.eval (t/ω)*Complex.exp ((μ/ω)*t) / q β t ^ m =
      (P.eval (t/ω)*Complex.exp ((μ/ω-(m:ℂ))*t)) / t^((β*(m:ℝ):ℝ):ℂ) := by
  rw [q, mul_pow, ← Complex.exp_nat_mul]
  have he : (μ/ω-(m:ℂ))*t = (μ/ω)*t-(m:ℂ)*t := by ring
  rw [he, Complex.exp_sub]
  rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.cpow_mul_nat]
  field_simp

/-- Division by a nonnegative real power preserves a strip-exponential decay. -/
lemma subcritical_term_limit (P : Polynomial ℂ) (μ ω : ℂ) (hω : ω ≠ 0)
    (β : ℝ) (hβ : 0 ≤ β) (m : ℕ) (hgap : (μ/ω).re < (m:ℝ))
    (y : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ r ≥ 1, |y r| ≤ B) :
    Tendsto (fun r : ℝ => P.eval (stripPoint y r/ω)*
      Complex.exp ((μ/ω)*stripPoint y r) / q β (stripPoint y r)^m) atTop (𝓝 0) := by
  have hu := FrequencyDecay.subcritical_frequency_uniform (univ : Set Unit) P μ ω hω
    (m:ℝ) hgap hB (fun r _ => y r) (fun r hr _ _ => hy r hr)
  have ht : Tendsto (fun r : ℝ => P.eval (stripPoint y r/ω)*
      Complex.exp ((μ/ω-(m:ℂ))*stripPoint y r)) atTop (𝓝 0) := by
    simpa [stripPoint] using hu.tendsto_at (mem_univ ())
  rw [tendsto_zero_iff_norm_tendsto_zero] at ht ⊢
  apply squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) _ ht
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  rw [term_cancel, norm_div, Complex.norm_cpow_real]
  have hnorm : 1 ≤ ‖stripPoint y r‖ :=
    hr.trans (by simpa [stripPoint_re, id] using Complex.re_le_norm (stripPoint y r))
  have hp : 1 ≤ ‖stripPoint y r‖ ^ (β*(m:ℝ)) :=
    Real.one_le_rpow hnorm (mul_nonneg hβ (Nat.cast_nonneg _))
  exact div_le_self (norm_nonneg _) hp

variable {n : ℕ}

lemma scaledLeadingCoefficient_eq_div (E : EquationData n) (S : Selection E) (j : Fin n) :
    scaledLeadingCoefficient E S j =
      ((selectedPolynomial E S j).leadingCoeff * (S.ω ^ multiplierDegree E S j)⁻¹) /
        S.ω ^ gap j := by
  have hh : gap j + j.val = n := Nat.sub_add_cancel j.isLt.le
  have hh' : (gap j : ℤ)+(j.val : ℤ) = (n : ℤ) := by exact_mod_cast hh
  have he : (j.val:ℤ)-(n:ℤ)-(multiplierDegree E S j:ℤ) =
      -((gap j+multiplierDegree E S j:ℕ):ℤ) := by
    simp only [Nat.cast_add]
    omega
  rw [scaledLeadingCoefficient, he, zpow_neg, zpow_natCast, pow_add]
  ring

def frequencyTerm (E : EquationData n) (S : Selection E) (j : Fin n) (μ t : ℂ) : ℂ :=
  (E.multipliers j μ).eval (t/S.ω) * Complex.exp ((μ/S.ω)*t) /
    (S.ω^gap j * q (beta E S:ℝ) t ^ gap j)

lemma selected_frequency_limit (E : EquationData n) (S : Selection E) (j : Fin n)
    (hμ : (gap j:ℂ)*S.ω ∈ E.frequencies j) (y : ℝ → ℝ) :
    Tendsto (fun r : ℝ => frequencyTerm E S j ((gap j:ℂ)*S.ω) (stripPoint y r))
      atTop (𝓝 (characteristicCoefficient E S j)) := by
  classical
  have hj : j ∈ selectedRows E S := (mem_selectedRows E S j).mpr hμ
  have hb := degree_bound_real E S hj
  have ht := PolynomialLimits.selected_natural_frequency_limit (stripPoint_norm_tendsto y)
    (selectedPolynomial E S j) S.ω S.spec.2.1 (beta E S:ℝ) (gap j) hb
  have ht' := ht.div_const (S.ω^gap j)
  have hfun : (fun r : ℝ => ((selectedPolynomial E S j).eval (stripPoint y r/S.ω) *
      Complex.exp ((gap j:ℂ)*stripPoint y r) / q (beta E S:ℝ) (stripPoint y r)^gap j) /
      S.ω^gap j) = (fun r => frequencyTerm E S j ((gap j:ℂ)*S.ω) (stripPoint y r)) := by
    funext r
    simp only [frequencyTerm, selectedPolynomial, mul_div_cancel_right₀ _ S.spec.2.1, q]
    ring
  change Tendsto (fun r : ℝ => ((selectedPolynomial E S j).eval (stripPoint y r/S.ω) *
      Complex.exp ((gap j:ℂ)*stripPoint y r) / q (beta E S:ℝ) (stripPoint y r)^gap j) /
      S.ω^gap j) atTop _ at ht'
  rw [hfun] at ht'
  by_cases ha : j ∈ attainingRows E S
  · have he := attaining_degree_eq_real E S ha
    simp only [multiplierDegree] at he
    rw [if_pos he] at ht'
    simpa only [characteristicCoefficient, if_pos ha, scaledLeadingCoefficient_eq_div, multiplierDegree] using ht'
  · have he := nonattaining_degree_lt_real E S hj ha
    simp only [multiplierDegree] at he
    rw [if_neg (ne_of_lt he), zero_div] at ht'
    simpa only [characteristicCoefficient, if_neg ha] using ht'

lemma subcritical_frequency_limit (E : EquationData n) (S : Selection E) (j : Fin n)
    {μ : ℂ} (hμ : μ ∈ E.frequencies j) (hne : μ ≠ (gap j:ℂ)*S.ω)
    (y : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ r ≥ 1, |y r| ≤ B) :
    Tendsto (fun r : ℝ => frequencyTerm E S j μ (stripPoint y r)) atTop (𝓝 0) := by
  have ht := (subcritical_term_limit (E.multipliers j μ) μ S.ω S.spec.2.1
    (beta E S:ℝ) (beta_real_nonneg E S) (gap j)
    (normalized_frequency_re_lt E S j hμ hne) y hB hy).div_const (S.ω^gap j)
  simp only [zero_div] at ht
  apply ht.congr
  intro r
  unfold frequencyTerm
  ring

lemma actual_frequency_limit (E : EquationData n) (S : Selection E) (j : Fin n)
    {μ : ℂ} (hμ : μ ∈ E.frequencies j)
    (y : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ r ≥ 1, |y r| ≤ B) :
    Tendsto (fun r : ℝ => frequencyTerm E S j μ (stripPoint y r)) atTop
      (𝓝 (if μ = (gap j:ℂ)*S.ω then characteristicCoefficient E S j else 0)) := by
  by_cases he : μ = (gap j:ℂ)*S.ω
  · subst μ
    simp only [ite_true]
    exact selected_frequency_limit E S j hμ y
  · rw [if_neg he]
    exact subcritical_frequency_limit E S j hμ he y hB hy

lemma normalizedCoefficient_eq_sum (E : EquationData n) (S : Selection E) (j : Fin n)
    (t : ℂ) :
    ScaledEquation.normalizedCoefficient E S.ω j t / q (beta E S:ℝ) t ^ gap j =
      ∑ μ ∈ E.frequencies j, frequencyTerm E S j μ t := by
  unfold ScaledEquation.normalizedCoefficient EquationData.coefficient
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro μ hμ
  have he : μ*(t/S.ω) = (μ/S.ω)*t := by ring
  rw [he]
  unfold frequencyTerm
  simp only [gap]
  ring

/-- The original finite exponential-polynomial coefficient, with both actual
normalizations, tends to its constructed characteristic coefficient on any
bounded horizontal strip path. No coefficient-limit hypothesis is added. -/
theorem normalizedCoefficient_limit (E : EquationData n) (S : Selection E) (j : Fin n)
    (y : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ r ≥ 1, |y r| ≤ B) :
    Tendsto (fun r : ℝ => ScaledEquation.normalizedCoefficient E S.ω j (stripPoint y r) /
      q (beta E S:ℝ) (stripPoint y r)^gap j) atTop
      (𝓝 (characteristicCoefficient E S j)) := by
  classical
  have ht : Tendsto (fun r : ℝ => ∑ μ ∈ E.frequencies j,
      frequencyTerm E S j μ (stripPoint y r)) atTop
      (𝓝 (∑ μ ∈ E.frequencies j, if μ = (gap j:ℂ)*S.ω then
        characteristicCoefficient E S j else 0)) := by
    apply tendsto_finsetSum
    intro μ hμ
    exact actual_frequency_limit E S j hμ y hB hy
  have he : (∑ μ ∈ E.frequencies j, if μ = (gap j:ℂ)*S.ω then
      characteristicCoefficient E S j else 0) = characteristicCoefficient E S j := by
    by_cases hm : (gap j:ℂ)*S.ω ∈ E.frequencies j
    · simp [hm]
    · have hn : j ∉ attainingRows E S := by
        intro hh
        exact hm ((mem_selectedRows E S j).mp ((mem_attainingRows E S j).mp hh).1)
      simp [characteristicCoefficient, hn]
  rw [he] at ht
  apply ht.congr
  intro r
  exact (normalizedCoefficient_eq_sum E S j (stripPoint y r)).symm

/-- The same actual coefficient limit using the analytic phase derivative
exp(β log t+t), as required by the exact nonlinear chain rule. -/
theorem normalizedCoefficient_phaseDerivative_limit (E : EquationData n) (S : Selection E)
    (j : Fin n) (y : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ r ≥ 1, |y r| ≤ B) :
    Tendsto (fun r : ℝ => ScaledEquation.normalizedCoefficient E S.ω j (stripPoint y r) /
      PhaseDerivativeBounds.phaseDerivative (beta E S:ℂ) (stripPoint y r)^gap j)
      atTop (𝓝 (characteristicCoefficient E S j)) := by
  apply (normalizedCoefficient_limit E S j y hB hy).congr'
  filter_upwards [(stripPoint_norm_tendsto y).eventually_gt_atTop 0] with r hr
  rw [q_eq_phaseDerivative (norm_pos_iff.mp hr)]
  norm_cast


/-- Arbitrary bounded strip paths detect uniform convergence on the entire
closed strip. This is a genuine choice argument, not a uniform-limit premise. -/
lemma uniformlyOn_strip_of_all_paths {F : ℝ → ℝ → ℂ} {c : ℂ} {B : ℝ}
    (hB : 0 ≤ B)
    (hpaths : ∀ y : ℝ → ℝ, (∀ r ≥ 1, |y r| ≤ B) →
      Tendsto (fun r => F r (y r)) atTop (𝓝 c)) :
    TendstoUniformlyOn F (fun _ => c) atTop (Icc (-B) B) := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let bad (r : ℝ) : Prop := ∃ v : ℝ, |v| ≤ B ∧ ε ≤ dist (F r v) c
  let y (r : ℝ) : ℝ := if h : bad r then h.choose else 0
  have hy : ∀ r ≥ 1, |y r| ≤ B := by
    intro r hr
    dsimp [y]
    split_ifs with hb
    · exact hb.choose_spec.1
    · simpa using hB
  have ht := hpaths y hy
  have hm : ∀ᶠ r in atTop, dist (F r (y r)) c < ε :=
    ht.eventually (Metric.ball_mem_nhds c hε)
  filter_upwards [hm] with r hr
  intro v hv
  rw [dist_comm]
  by_contra hn
  have hb : bad r := ⟨v, abs_le.mpr hv, le_of_not_gt hn⟩
  have hh : ε ≤ dist (F r (y r)) c := by
    simpa only [y, dif_pos hb] using hb.choose_spec.2
  exact (not_le_of_gt hr) hh

/-- Uniform limit on every bounded horizontal strip, for the actual finite
exponential-polynomial coefficient and any maximal-frequency selection. -/
theorem normalizedCoefficient_uniform (E : EquationData n) (S : Selection E) (j : Fin n)
    {B : ℝ} (hB : 0 ≤ B) :
    TendstoUniformlyOn (fun (r : ℝ) (v : ℝ) =>
      ScaledEquation.normalizedCoefficient E S.ω j ((r:ℂ)+(v:ℂ)*Complex.I) /
        PhaseDerivativeBounds.phaseDerivative (beta E S:ℂ)
          ((r:ℂ)+(v:ℂ)*Complex.I)^gap j)
      (fun _ => characteristicCoefficient E S j) atTop (Icc (-B) B) := by
  apply uniformlyOn_strip_of_all_paths hB
  intro y hy
  exact normalizedCoefficient_phaseDerivative_limit E S j y hB hy

/-- Natural-order extension for the exact chain-rule coefficient formulas. -/
def actualB (E : EquationData n) (S : Selection E) (j : ℕ) (t : ℂ) : ℂ :=
  if h : j < n then ScaledEquation.normalizedCoefficient E S.ω ⟨j,h⟩ t else 0

def actualC (E : EquationData n) (S : Selection E) (j : ℕ) : ℂ :=
  if h : j < n then characteristicCoefficient E S ⟨j,h⟩ else 0

/-- Actual phase-coefficient limits, with the prescribed derivative identity
required only in the right half-plane where the primitive is defined. -/
theorem phaseCoefficient_actual_limit (E : EquationData n) (S : Selection E)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ z : ℂ, 0 < z.re → deriv Φ z =
      PhaseDerivativeBounds.phaseDerivative ((beta E S:ℝ):ℂ) z)
    (k : Fin n) (y : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hy : ∀ r ≥ 1, |y r| ≤ B) :
    Tendsto (fun r : ℝ => ExactChange.phaseCoeff n (actualB E S) Φ k.val (stripPoint y r))
      atTop (𝓝 (characteristicCoefficient E S k)) := by
  have hre : Tendsto (fun r : ℝ => (stripPoint y r).re) atTop atTop := by
    simp_rw [stripPoint_re]
    exact tendsto_id
  have hdom : ∀ᶠ r in atTop, stripPoint y r ∈ {z : ℂ | 0 < z.re} := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    simpa only [mem_ofPred_eq, stripPoint_re] using hr
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have ht := PhaseDerivativeBounds.prescribed_phaseCoeff_limit_on
    (c := actualC E S) (B := actualB E S) k.isLt (beta_real_nonneg E S) hopen
    (fun z hz => hΦ z hz) hre hdom
  have hnorm : ∀ j < n, Tendsto (fun r : ℝ => actualB E S j (stripPoint y r) /
      deriv Φ (stripPoint y r)^(n-j)) atTop (𝓝 (actualC E S j)) := by
    intro j hj
    simp only [actualC, dif_pos hj]
    apply (normalizedCoefficient_phaseDerivative_limit E S ⟨j,hj⟩ y hB hy).congr'
    filter_upwards [hdom] with r hr
    simp only [actualB, dif_pos hj, gap]
    rw [hΦ (stripPoint y r) hr]
    norm_cast
  have hfinal := ht hnorm
  simpa only [actualC, dif_pos k.isLt, Fin.eta] using hfinal

/-- Uniform convergence of the actual chain-rule phase coefficients throughout
any fixed bounded horizontal strip inside the phase primitive's domain. -/
theorem phaseCoefficient_actual_uniform (E : EquationData n) (S : Selection E)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ z : ℂ, 0 < z.re → deriv Φ z =
      PhaseDerivativeBounds.phaseDerivative ((beta E S:ℝ):ℂ) z)
    (k : Fin n) {B : ℝ} (hB : 0 ≤ B) :
    TendstoUniformlyOn (fun (r : ℝ) (v : ℝ) =>
      ExactChange.phaseCoeff n (actualB E S) Φ k.val ((r:ℂ)+(v:ℂ)*Complex.I))
      (fun _ => characteristicCoefficient E S k) atTop (Icc (-B) B) := by
  apply uniformlyOn_strip_of_all_paths hB
  intro y hy
  exact phaseCoefficient_actual_limit E S Φ hΦ k y hB hy

/-- Explicit epsilon interface for the normalized original coefficients. -/
theorem normalizedCoefficient_uniform_epsilon (E : EquationData n) (S : Selection E)
    (j : Fin n) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ v : ℝ, |v| ≤ B →
      ‖ScaledEquation.normalizedCoefficient E S.ω j ((r:ℂ)+(v:ℂ)*Complex.I) /
        PhaseDerivativeBounds.phaseDerivative (beta E S:ℂ)
          ((r:ℂ)+(v:ℂ)*Complex.I)^gap j - characteristicCoefficient E S j‖ < ε := by
  have ht := (Metric.tendstoUniformlyOn_iff.mp (normalizedCoefficient_uniform E S j hB)) ε hε
  filter_upwards [ht] with r hr
  intro v hv
  have hh := hr v (abs_le.mp hv)
  rw [dist_comm, dist_eq_norm] at hh
  exact hh

/-- Epsilon form of the full transformed-coefficient uniform limit. -/
theorem phaseCoefficient_actual_uniform_epsilon (E : EquationData n) (S : Selection E)
    (Φ : ℂ → ℂ)
    (hΦ : ∀ z : ℂ, 0 < z.re → deriv Φ z =
      PhaseDerivativeBounds.phaseDerivative ((beta E S:ℝ):ℂ) z)
    (k : Fin n) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, ∀ v : ℝ, |v| ≤ B →
      ‖ExactChange.phaseCoeff n (actualB E S) Φ k.val ((r:ℂ)+(v:ℂ)*Complex.I) -
        characteristicCoefficient E S k‖ < ε := by
  have ht := (Metric.tendstoUniformlyOn_iff.mp
    (phaseCoefficient_actual_uniform E S Φ hΦ k hB)) ε hε
  filter_upwards [ht] with r hr
  intro v hv
  have hh := hr v (abs_le.mp hv)
  rw [dist_comm, dist_eq_norm] at hh
  exact hh

#print axioms phaseCoefficient_actual_uniform_epsilon
#print axioms phaseCoefficient_actual_limit
#print axioms phaseCoefficient_actual_uniform
#print axioms normalizedCoefficient_uniform_epsilon
#print axioms uniformlyOn_strip_of_all_paths
#print axioms normalizedCoefficient_uniform
#print axioms subcritical_term_limit
#print axioms selected_frequency_limit
#print axioms subcritical_frequency_limit
#print axioms normalizedCoefficient_limit
#print axioms normalizedCoefficient_phaseDerivative_limit
end ZeroDensity.NormalizedCoefficientLimits
