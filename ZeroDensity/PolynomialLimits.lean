import ZeroDensity.FrequencyDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Leading-term limits of actual complex polynomials. The proof expands the
finite coefficient sum and proves every strict degree gap tends to zero. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators
namespace ZeroDensity.PolynomialLimits

theorem degree_gap_ratio {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) {n d : ℕ} (hnd : n < d) :
    Tendsto (fun a => (t a)^n/(t a)^d) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hh : Tendsto (fun a => ‖t a‖ ^ (-((d:ℝ)-(n:ℝ)))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr (by exact_mod_cast hnd : (n:ℝ)<(d:ℝ)))).comp ht
  apply hh.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with a ha
  rw [norm_div,norm_pow,norm_pow]
  have he : -((d:ℝ)-(n:ℝ)) = (n:ℝ)-(d:ℝ) := by ring
  rw [he,Real.rpow_sub ha,Real.rpow_natCast,Real.rpow_natCast]

theorem scaled_monomial_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) (ω : ℂ) (hω : ω ≠ 0)
    {n d : ℕ} (hnd : n ≤ d) :
    Tendsto (fun a => (t a/ω)^n/(t a)^d) l
      (𝓝 (if n=d then (ω^n)⁻¹ else 0)) := by
  by_cases he : n=d
  · subst n
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [ht.eventually_gt_atTop 0] with a ha
    have hta : t a ≠ 0 := norm_pos_iff.mp ha
    rw [div_pow]
    field_simp
  · have hn : n<d := lt_of_le_of_ne hnd he
    have hh := (degree_gap_ratio ht hn).mul_const ((ω^n)⁻¹)
    have hh' : Tendsto (fun a => ((t a)^n/(t a)^d)*(ω^n)⁻¹) l (𝓝 0) := by simpa using hh
    rw [if_neg he]
    apply hh'.congr'
    exact Eventually.of_forall (fun a => by dsimp; rw [div_pow]; ring)

/-- Leading-term normalization, valid along any filter escaping to infinity. -/
theorem polynomial_leading_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) (P : Polynomial ℂ)
    (ω : ℂ) (hω : ω ≠ 0) :
    Tendsto (fun a => P.eval (t a/ω)/(t a)^P.natDegree) l
      (𝓝 (P.leadingCoeff*(ω^P.natDegree)⁻¹)) := by
  have hh : Tendsto (fun a => ∑ n ∈ Finset.range (P.natDegree+1),
      P.coeff n*((t a/ω)^n/(t a)^P.natDegree)) l
      (𝓝 (∑ n ∈ Finset.range (P.natDegree+1),
        P.coeff n*(if n=P.natDegree then (ω^n)⁻¹ else 0))) := by
    apply tendsto_finsetSum
    intro n hn
    exact (scaled_monomial_limit ht ω hω (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).const_mul (P.coeff n)
  have he : (∑ n ∈ Finset.range (P.natDegree+1),
      P.coeff n*(if n=P.natDegree then (ω^n)⁻¹ else 0)) =
      P.leadingCoeff*(ω^P.natDegree)⁻¹ := by
    rw [Finset.sum_eq_single P.natDegree]
    · simp only [ite_true, Polynomial.coeff_natDegree]
    · intro n hn hne; simp [hne]
    · simp
  rw [he] at hh
  apply hh.congr
  intro a
  rw [Polynomial.eval_eq_sum_range,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- A strict real degree gap tends to zero. For real exponents the complex
power norm identity holds even without a slit-plane hypothesis. -/
theorem real_degree_gap_ratio {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) {n : ℕ} {b : ℝ}
    (hnb : (n:ℝ)<b) :
    Tendsto (fun a => (t a)^n/(t a)^(b:ℂ)) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hh : Tendsto (fun a => ‖t a‖ ^ (-(b-(n:ℝ)))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hnb)).comp ht
  apply hh.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with a ha
  rw [norm_div,norm_pow,Complex.norm_cpow_real]
  have he : -(b-(n:ℝ)) = (n:ℝ)-b := by ring
  rw [he,Real.rpow_sub ha,Real.rpow_natCast]

/-- Strictly lower polynomial degrees vanish under real complex-power
normalization. The polynomial itself, rather than a growth assumption, is
used in the proof. -/
theorem polynomial_strict_degree_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) (P : Polynomial ℂ)
    (ω : ℂ) (hω : ω ≠ 0) {b : ℝ} (hdb : (P.natDegree:ℝ)<b) :
    Tendsto (fun a => P.eval (t a/ω)/(t a)^(b:ℂ)) l (𝓝 0) := by
  have hh := (polynomial_leading_limit ht P ω hω).mul (real_degree_gap_ratio ht hdb)
  have hh' : Tendsto (fun a => (P.eval (t a/ω)/(t a)^P.natDegree) *
      ((t a)^P.natDegree/(t a)^(b:ℂ))) l (𝓝 0) := by simpa using hh
  apply hh'.congr'
  filter_upwards [ht.eventually_gt_atTop 0] with a ha
  have hta : t a ≠ 0 := norm_pos_iff.mp ha
  field_simp

/-- Selected-frequency degree edge: equality gives the actual leading
coefficient; a strict gap gives zero. No rationality assumption is needed. -/
theorem polynomial_real_degree_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) (P : Polynomial ℂ)
    (ω : ℂ) (hω : ω ≠ 0) {b : ℝ} (hdb : (P.natDegree:ℝ)≤b) :
    Tendsto (fun a => P.eval (t a/ω)/(t a)^(b:ℂ)) l
      (𝓝 (if (P.natDegree:ℝ)=b then P.leadingCoeff*(ω^P.natDegree)⁻¹ else 0)) := by
  rcases eq_or_lt_of_le hdb with he | hl
  · simp only [he,ite_true]
    have hb : (b:ℂ) = (P.natDegree:ℂ) := by rw [←he]; simp
    simpa only [hb,Complex.cpow_natCast] using polynomial_leading_limit ht P ω hω
  · rw [if_neg (ne_of_lt hl)]
    exact polynomial_strict_degree_limit ht P ω hω hl

/-- Exact cancellation for a natural selected phase frequency. Real
noninteger frequencies require additional branch geometry and are not
asserted in this cancellation lemma. -/
theorem selected_term_cancel (A t : ℂ) (β : ℝ) (m : ℕ) :
    A*Complex.exp ((m:ℂ)*t) / ((t^(β:ℂ)*Complex.exp t)^m) =
      A/t^((β*(m:ℝ):ℝ):ℂ) := by
  rw [mul_pow,Complex.exp_nat_mul,
    mul_div_mul_right A _ (pow_ne_zero m (Complex.exp_ne_zero t))]
  rw [Complex.ofReal_mul,Complex.ofReal_natCast,Complex.cpow_mul_nat]

/-- Actual selected-frequency term after exact q(t)^m cancellation. -/
theorem selected_natural_frequency_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun a => ‖t a‖) l atTop) (P : Polynomial ℂ)
    (ω : ℂ) (hω : ω ≠ 0) (β : ℝ) (m : ℕ)
    (hdb : (P.natDegree:ℝ)≤β*(m:ℝ)) :
    Tendsto (fun a => P.eval (t a/ω)*Complex.exp ((m:ℂ)*t a) /
      (((t a)^(β:ℂ)*Complex.exp (t a))^m)) l
      (𝓝 (if (P.natDegree:ℝ)=β*(m:ℝ) then
        P.leadingCoeff*(ω^P.natDegree)⁻¹ else 0)) := by
  exact (polynomial_real_degree_limit ht P ω hω hdb).congr
    (fun a => (selected_term_cancel (P.eval (t a/ω)) (t a) β m).symm)

#print axioms selected_natural_frequency_limit
#print axioms polynomial_real_degree_limit
#print axioms polynomial_strict_degree_limit
#print axioms polynomial_leading_limit
end ZeroDensity.PolynomialLimits
