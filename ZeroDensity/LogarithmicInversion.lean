import ZeroDensity.PhasePrimitiveRemainder
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Inversion of t + beta log t with a vanishing complex error. The input is
an exact logarithmic equation, not an asserted inverse asymptotic. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.LogarithmicInversion
open ZeroDensity.MainTheorem

lemma complex_log_div_limit {ι : Type*} {l : Filter ι} {t : ι → ℂ}
    (ht : Tendsto (fun x => ‖t x‖) l atTop) :
    Tendsto (fun x => Complex.log (t x)/t x) l (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht
  have hconst : Tendsto (fun x => Real.pi/‖t x‖) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have hb : Tendsto (fun x => Real.log ‖t x‖/‖t x‖+Real.pi/‖t x‖) l (𝓝 0) := by
    simpa only [zero_add, Function.comp_apply, id_eq] using hlog.add hconst
  apply squeeze_zero_norm' ?_ hb
  filter_upwards [ht.eventually_ge_atTop 1] with x hx
  have hp : 0 < ‖t x‖ := by linarith
  rw [norm_div]
  have hh := Complex.norm_le_abs_re_add_abs_im (Complex.log (t x))
  rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hx)] at hh
  have hb := hh.trans (add_le_add_right (Complex.abs_arg_le_pi (t x)) _)
  calc
    _ ≤ (Real.log ‖t x‖+Real.pi)/‖t x‖ := div_le_div_of_nonneg_right hb hp.le
    _ = _ := add_div _ _ _

lemma log_difference_of_right_ratio {t L : ℂ} (hL : 0 < L.re) (hr : 0 < (t/L).re) :
    Complex.log t-Complex.log L = Complex.log (t/L) := by
  have hLn : L ≠ 0 := Complex.slitPlane_ne_zero (Or.inl hL)
  have hrn : t/L ≠ 0 := Complex.slitPlane_ne_zero (Or.inl hr)
  have ha := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)
  have hb := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hL)
  have hm : Complex.arg (t/L)+Complex.arg L ∈ Ioc (-Real.pi) Real.pi := by
    have aa := abs_lt.mp ha
    have bb := abs_lt.mp hb
    constructor <;> linarith
  have he := Complex.log_mul hrn hLn hm
  rw [div_mul_cancel₀ _ hLn] at he
  linear_combination he

/-- Once a single logarithmic branch index is fixed, inversion with o(1)
error follows for arbitrary real beta. -/
theorem invert_log_equation {ι : Type*} {l : Filter ι} {t L e : ι → ℂ}
    (β : ℝ) (K : ℂ) (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hL : ∀ᶠ x in l, 0 < (L x).re) (he : Tendsto e l (𝓝 0))
    (heq : ∀ᶠ x in l, t x+(β:ℂ)*Complex.log (t x)+e x = L x+K) :
    Tendsto (fun x => t x-(L x-(β:ℂ)*Complex.log (L x)+K)) l (𝓝 0) := by
  have hi : Tendsto (fun x => (t x)⁻¹) l (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp ht)
  have hl := complex_log_div_limit ht
  have hex : Tendsto (fun x => e x/t x) l (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using he.mul hi
  have hkx : Tendsto (fun x => K/t x) l (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using (tendsto_const_nhds (x := K)).mul hi
  have hβx : Tendsto (fun x => (β:ℂ)*(Complex.log (t x)/t x)) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := (β:ℂ))).mul hl
  have hLt : Tendsto (fun x => L x/t x) l (𝓝 1) := by
    have hh := (((tendsto_const_nhds (x := (1:ℂ))).add hβx).add hex).sub hkx
    simp only [add_zero, sub_zero] at hh
    apply hh.congr'
    filter_upwards [heq, ht.eventually_gt_atTop 0] with x hx hn
    have htn : t x ≠ 0 := norm_pos_iff.mp hn
    have ha : L x = t x+(β:ℂ)*Complex.log (t x)+e x-K := by linear_combination -hx
    rw [ha]
    field_simp
    <;> ring
  have htL : Tendsto (fun x => t x/L x) l (𝓝 1) := by
    have hh := hLt.inv₀ (by norm_num : (1:ℂ) ≠ 0)
    simpa only [inv_div, inv_one] using hh
  have hr : ∀ᶠ x in l, 0 < (t x/L x).re := by
    have hh := Complex.continuous_re.continuousAt.tendsto.comp htL
    exact hh.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < (1:ℂ).re))
  have hlog : Tendsto (fun x => Complex.log (t x)-Complex.log (L x)) l (𝓝 0) := by
    have hc : ContinuousAt Complex.log (1:ℂ) :=
      (analyticAt_clog (by simp : (1:ℂ) ∈ Complex.slitPlane)).continuousAt
    have hh : Tendsto (fun x => Complex.log (t x/L x)) l (𝓝 0) := by
      convert hc.tendsto.comp htL using 1 <;> first | rfl | simp
    apply hh.congr'
    filter_upwards [hL,hr] with x hx hy
    exact (log_difference_of_right_ratio hx hy).symm
  have hh := ((tendsto_const_nhds (x := (-(β:ℂ)))).mul hlog).sub he
  simp only [mul_zero, sub_zero] at hh
  apply hh.congr'
  filter_upwards [heq] with x hx
  linear_combination -hx
end ZeroDensity.LogarithmicInversion
