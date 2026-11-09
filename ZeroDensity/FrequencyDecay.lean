import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-! Actual polynomial exponential terms on bounded horizontal strips.
The estimates are derived from the coefficients and the real-part gap. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators
namespace ZeroDensity.FrequencyDecay

def coeffMass (P : Polynomial ℂ) : ℝ := ∑ n ∈ P.support, ‖P.coeff n‖

theorem polynomial_norm_bound (P : Polynomial ℂ) (z : ℂ) :
    ‖P.eval z‖ ≤ coeffMass P * (1+‖z‖)^P.natDegree := by
  rw [Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  calc
    ‖∑ n ∈ P.support, P.coeff n*z^n‖ ≤ ∑ n ∈ P.support, ‖P.coeff n*z^n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ P.support, ‖P.coeff n‖*(1+‖z‖)^P.natDegree := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hn' : n ≤ P.natDegree := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
      calc
        ‖z‖^n ≤ (1+‖z‖)^n := pow_le_pow_left₀ (norm_nonneg _) (by linarith [norm_nonneg z]) n
        _ ≤ _ := pow_le_pow_right₀ (by linarith [norm_nonneg z]) hn'
    _ = _ := by rw [coeffMass, Finset.sum_mul]

/-- Exact exponential estimate; the imaginary part costs only a constant. -/
theorem exponential_strip_bound {ν : ℂ} {δ r y B : ℝ}
    (hgap : ν.re = -δ) (hy : |y| ≤ B) :
    ‖Complex.exp (ν*((r:ℂ)+(y:ℂ)*Complex.I))‖ ≤
      Real.exp (|ν.im| *B-δ*r) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (ν*((r:ℂ)+(y:ℂ)*Complex.I)).re = -δ*r-ν.im*y := by
    simp [Complex.mul_re,hgap]
  rw [hre]
  have hh : |ν.im*y| ≤ |ν.im| *B := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  have ha := neg_le_abs (ν.im*y)
  linarith

/-- Explicit polynomial bound after division by a nonzero phase coefficient. -/
theorem polynomial_horizontal_bound (P : Polynomial ℂ) (ω : ℂ) (hω : ω ≠ 0)
    {r y B : ℝ} (hr : 0 ≤ r) (hB : 0 ≤ B) (hy : |y| ≤ B) :
    ‖P.eval (((r:ℂ)+(y:ℂ)*Complex.I)/ω)‖ ≤
      (coeffMass P * (1+(1+B)/‖ω‖)^P.natDegree) * (1+r)^P.natDegree := by
  have hωn : 0 < ‖ω‖ := norm_pos_iff.mpr hω
  have ht : ‖((r:ℂ)+(y:ℂ)*Complex.I)/ω‖ ≤ (r+B)/‖ω‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hωn.le
    have hh := norm_add_le (r:ℂ) ((y:ℂ)*Complex.I)
    simpa [norm_mul, abs_of_nonneg hr] using hh.trans (by
      simpa [norm_mul, abs_of_nonneg hr] using add_le_add_left hy r)
  have hlarge : 1+‖((r:ℂ)+(y:ℂ)*Complex.I)/ω‖ ≤
      (1+(1+B)/‖ω‖)*(1+r) := by
    have hd : 0 ≤ (1+B)/‖ω‖ := div_nonneg (by linarith) hωn.le
    have hh : (r+B)/‖ω‖ ≤ ((1+B)/‖ω‖)*(1+r) := by
      apply (div_le_iff₀ hωn).mpr
      field_simp
      nlinarith
    nlinarith
  calc
    _ ≤ coeffMass P * (1+‖((r:ℂ)+(y:ℂ)*Complex.I)/ω‖)^P.natDegree := polynomial_norm_bound _ _
    _ ≤ coeffMass P * ((1+(1+B)/‖ω‖)*(1+r))^P.natDegree :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlarge _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := by rw [mul_pow]; ring

/-- Uniform decay of every actual polynomial exponential term on bounded
horizontal strips, for a strictly negative real-part gap. -/
theorem polynomial_exponential_uniform {ι : Type*} (D : Set ι)
    (P : Polynomial ℂ) (ω : ℂ) (hω : ω ≠ 0) (ν : ℂ)
    {δ B : ℝ} (hδ : 0 < δ) (hgap : ν.re = -δ) (hB : 0 ≤ B)
    (y : ℝ → ι → ℝ) (hy : ∀ r ≥ 1, ∀ θ ∈ D, |y r θ| ≤ B) :
    TendstoUniformlyOn (fun (r : ℝ) θ =>
      P.eval (((r:ℂ)+(y r θ:ℂ)*Complex.I)/ω) *
        Complex.exp (ν*((r:ℂ)+(y r θ:ℂ)*Complex.I)))
      (fun _ => 0) atTop D := by
  let K := coeffMass P * (1+(1+B)/‖ω‖)^P.natDegree
  have hK : 0 ≤ K := by
    dsimp [K,coeffMass]; positivity
  let C := |ν.im| * B
  let M := K*(2:ℝ)^P.natDegree*Real.exp C
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ht : Tendsto (fun r : ℝ => M*(r^P.natDegree*Real.exp (-δ*r))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (P.natDegree:ℝ) δ hδ).const_mul M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop (1:ℝ), ht.eventually (gt_mem_nhds hε)] with r hr he
  intro θ hθ
  rw [dist_zero_left, norm_mul]
  have hp := polynomial_horizontal_bound P ω hω (zero_le_one.trans hr) hB (hy r hr θ hθ)
  have hpp : ‖P.eval (((r:ℂ)+(y r θ:ℂ)*Complex.I)/ω)‖ ≤
      K*(2:ℝ)^P.natDegree*r^P.natDegree := by
    have hh : 1+r ≤ 2*r := by linarith
    have hh' := pow_le_pow_left₀ (by linarith : 0 ≤ 1+r) hh P.natDegree
    have hh'' := mul_le_mul_of_nonneg_left hh' hK
    rw [mul_pow] at hh''
    exact hp.trans (by simpa [K,mul_assoc] using hh'')
  have hex := exponential_strip_bound (r := r) hgap (hy r hr θ hθ)
  have hex' : ‖Complex.exp (ν*((r:ℂ)+(y r θ:ℂ)*Complex.I))‖ ≤
      Real.exp C*Real.exp (-δ*r) := by
    have hid : |ν.im| * B-δ*r = C+(-δ*r) := by dsimp [C]; ring
    rw [hid, Real.exp_add] at hex
    exact hex
  have hh := mul_le_mul hpp hex' (norm_nonneg _) (by positivity : 0 ≤ K*(2:ℝ)^P.natDegree*r^P.natDegree)
  have hb : ‖P.eval (((r:ℂ)+(y r θ:ℂ)*Complex.I)/ω)‖ *
      ‖Complex.exp (ν*((r:ℂ)+(y r θ:ℂ)*Complex.I))‖ ≤
      M*(r^P.natDegree*Real.exp (-δ*r)) := by
    simpa [M,mul_assoc,mul_left_comm,mul_comm] using hh
  exact hb.trans_lt he

/-- The original frequency gap is exactly the negative real part needed by
the horizontal-strip estimate. -/
theorem frequency_gap {μ ω : ℂ} {m δ : ℝ}
    (hgap : m-(μ/ω).re = δ) : (μ/ω-(m:ℂ)).re = -δ := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

/-- Direct original-frequency form, with the gap derived from μ/ω. -/
theorem subcritical_frequency_uniform {ι : Type*} (D : Set ι)
    (P : Polynomial ℂ) (μ ω : ℂ) (hω : ω ≠ 0) (m : ℝ)
    (hgap : (μ/ω).re < m) {B : ℝ} (hB : 0 ≤ B)
    (y : ℝ → ι → ℝ) (hy : ∀ r ≥ 1, ∀ θ ∈ D, |y r θ| ≤ B) :
    TendstoUniformlyOn (fun (r : ℝ) θ =>
      P.eval (((r:ℂ)+(y r θ:ℂ)*Complex.I)/ω) *
        Complex.exp ((μ/ω-(m:ℂ))*((r:ℂ)+(y r θ:ℂ)*Complex.I)))
      (fun _ => 0) atTop D := by
  apply polynomial_exponential_uniform D P ω hω (μ/ω-(m:ℂ))
    (δ := m-(μ/ω).re) (sub_pos.mpr hgap) _ hB y hy
  exact frequency_gap rfl

#print axioms subcritical_frequency_uniform
#print axioms polynomial_exponential_uniform
#print axioms polynomial_horizontal_bound
#print axioms exponential_strip_bound
end ZeroDensity.FrequencyDecay
