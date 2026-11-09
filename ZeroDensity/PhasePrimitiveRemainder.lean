import ZeroDensity.PrimitiveIntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Uniform half-plane estimates for actual phase primitives. The straight
segment from 1 to t supplies a quantitative bound for the last remainder
in repeated integration by parts. No primitive asymptotic is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace ZeroDensity.PhasePrimitiveRemainder
open ZeroDensity.MainTheorem ZeroDensity.PrimitiveIntegrationByParts

def path (t : ℂ) (u : ℝ) : ℂ := (1-u:ℝ)+(u:ℂ)*t

lemma path_right {t : ℂ} (ht : t ∈ rightHalfPlane) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    path t u ∈ rightHalfPlane := by
  change 0 < (path t u).re
  simp only [path, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  change 0 < t.re at ht
  have hu1 := hu.2
  rcases eq_or_lt_of_le hu.1 with h | h
  · simp [←h]
  · nlinarith [mul_pos h ht]

lemma path_norm_lower {t : ℂ} (ht : t ∈ rightHalfPlane) (hρ : 1 ≤ ‖t‖)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (1+u*‖t‖)/4 ≤ ‖path t u‖ := by
  have hre : (path t u).re = 1-u+u*t.re := by simp [path]
  have him : (path t u).im = u*t.im := by simp [path]
  have ht0 : 0 < t.re := ht
  have hsq : ‖path t u‖^2 = (1-u)^2+u^2*‖t‖^2+2*u*(1-u)*t.re := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  have hu0 := hu.1
  have hu1 := hu.2
  have hpos : 0 ≤ 2*u*(1-u)*t.re := by positivity
  have hn : u*‖t‖ ≤ ‖path t u‖ := by
    nlinarith [norm_nonneg (path t u), norm_nonneg t, sq_nonneg (1-u)]
  have hc : 1-u ≤ ‖path t u‖ := by
    have := Complex.re_le_norm (path t u)
    nlinarith [mul_nonneg hu.1 ht0.le]
  have : u*(‖t‖-1) ≥ 0 := mul_nonneg hu.1 (by linarith)
  linarith

lemma path_re_upper {t : ℂ} (ht : t ∈ rightHalfPlane)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (path t u).re ≤ t.re+1 := by
  simp only [path, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  change 0 < t.re at ht
  have hu0 := hu.1
  nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) ht.le]

lemma path_hasDeriv (t : ℂ) (u : ℝ) : HasDerivAt (path t) (t-1) u := by
  have h := ((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id u)).ofReal_comp.add
    ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const t)
  convert h using 1 <;> first | rfl | (simp [path]; ring) <;> ring

/-- A fixed integrable envelope for every exponent below -2. -/
lemma phase_path_bound {α : ℝ} (hα : α ≤ -2) {t : ℂ}
    (ht : t ∈ rightHalfPlane) (hρ : 1 ≤ ‖t‖)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    ‖phaseDerivative α (path t u)‖ ≤
      4^(-α)*Real.exp (t.re+1)*(1+u*‖t‖)^(-2:ℤ) := by
  have hu0 := hu.1
  have hp : 0 < 1+u*‖t‖ := by positivity
  have hpn : path t u ≠ 0 := Complex.slitPlane_ne_zero (Or.inl (path_right ht hu))
  change ‖ZeroDensity.PhaseDerivativeBounds.phaseDerivative (α:ℂ) (path t u)‖ ≤ _
  rw [ZeroDensity.PhaseDerivativeBounds.norm_phaseDerivative α hpn]
  have ha := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1+u*‖t‖)/4)
    (path_norm_lower ht hρ hu) (by linarith : α ≤ 0)
  have hb : ((1+u*‖t‖)/4)^α = 4^(-α)*(1+u*‖t‖)^α := by
    rw [Real.div_rpow hp.le (by norm_num : (0:ℝ) ≤ 4), div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4), mul_comm]
  have hc : (1+u*‖t‖)^α ≤ (1+u*‖t‖)^(-2:ℤ) := by
    rw [←Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [mul_nonneg hu.1 (norm_nonneg t)]) (by exact_mod_cast hα)
  rw [hb] at ha
  calc
    _ ≤ (4^(-α)*(1+u*‖t‖)^(-2:ℤ))*Real.exp (t.re+1) :=
      mul_le_mul
        (ha.trans (mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg (by norm_num) _)))
        (Real.exp_le_exp.mpr (path_re_upper ht hu))
        (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

lemma envelope_integral (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ u in (0:ℝ)..1, ρ*(1+u*ρ)^(-2:ℤ)) = 1-(1+ρ)⁻¹ := by
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => -(1+u*ρ)⁻¹) (ρ*(1+u*ρ)^(-2:ℤ)) u := by
    have hu0 := hu.1
    have hn : 1+u*ρ ≠ 0 := ne_of_gt (by positivity)
    have hh := (((hasDerivAt_id u).mul_const ρ).const_add 1).inv hn |>.neg
    convert hh using 1 <;> first | rfl | (simp only [zpow_neg, zpow_ofNat, pow_two, id_eq, div_eq_mul_inv]; ring)
  have hc : ContinuousOn (fun u : ℝ => ρ*(1+u*ρ)^(-2:ℤ)) (Icc 0 1) := by
    intro u hu
    have hu0 := hu.1
    exact ((continuousAt_const.mul
      (((continuousAt_id.mul continuousAt_const).const_add 1).zpow₀ (-2)
        (Or.inl (ne_of_gt (by positivity : 0 < 1+u*ρ)))))).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hd u (by simpa [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hu)) ((by simpa [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hc :
      ContinuousOn _ (uIcc (0:ℝ) 1)).intervalIntegrable)
  simpa [sub_eq_add_neg, add_comm] using he

/-- The last integration-by-parts remainder is O(exp(Re t)) throughout
Re t > 0, |t| >= 1. The constant is independent of Im t. -/
theorem negative_phase_displacement {H : ℂ → ℂ} {α : ℝ} {A : ℂ}
    (hα : α ≤ -2)
    (hH : ∀ t ∈ rightHalfPlane, HasDerivAt H (A*phaseDerivative α t) t)
    {t : ℂ} (ht : t ∈ rightHalfPlane) (hρ : 1 ≤ ‖t‖) :
    ‖H t-H 1‖ ≤ 2*‖A‖*4^(-α)*Real.exp (t.re+1) := by
  let K : ℝ := 2*‖A‖*4^(-α)*Real.exp (t.re+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hd (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u => H (path t u))
        (A*phaseDerivative α (path t u)*(t-1)) u := by
    convert (hH _ (path_right ht hu)).complexToReal_fderiv.comp_hasDerivAt u
      (path_hasDeriv t u) using 1 <;> first | rfl | simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  have hb (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      ‖deriv (fun u => H (path t u)) u‖ ≤ K*(‖t‖*(1+u*‖t‖)^(-2:ℤ)) := by
    rw [(hd u hu).deriv, norm_mul, norm_mul]
    have hlen : ‖t-1‖ ≤ 2*‖t‖ := by
      have hh := norm_sub_le t (1:ℂ)
      simp only [norm_one] at hh
      linarith
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left (phase_path_bound hα ht hρ hu) (norm_nonneg A))
      hlen (norm_nonneg _) (by positivity)
    convert hh using 1 <;> first | rfl | (dsimp only [K]; ring)
  have hc : ContinuousOn (fun u : ℝ => K*(‖t‖*(1+u*‖t‖)^(-2:ℤ))) (Icc 0 1) := by
    intro u hu
    have hu0 := hu.1
    exact (continuousAt_const.mul (continuousAt_const.mul
      (((continuousAt_id.mul continuousAt_const).const_add 1).zpow₀ (-2)
        (Or.inl (ne_of_gt (by positivity : 0 < 1+u*‖t‖)))))).continuousWithinAt
  have hbound := norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num : (0:ℝ) ≤ 1)
    (fun u hu => (hd u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hd u ⟨hu.1.le,hu.2.le⟩).differentiableAt.differentiableWithinAt)
    (Filter.Eventually.of_forall (fun u hu => hb u ⟨hu.1.le,hu.2.le⟩))
    ((by simpa [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] using hc :
      ContinuousOn _ (uIcc (0:ℝ) 1)).intervalIntegrable)
  simp only [path, zero_mul, one_mul, sub_zero, sub_self, Complex.ofReal_one,
    Complex.ofReal_zero, zero_add, add_zero] at hbound
  rw [intervalIntegral.integral_const_mul, envelope_integral _ (by linarith)] at hbound
  exact hbound.trans (by nlinarith [inv_nonneg.mpr (by linarith : 0 ≤ 1+‖t‖)])

/-- Signed falling-factorial coefficients in the endpoint expansion. -/
def coefficient (β : ℝ) : ℕ → ℂ
  | 0 => 1
  | m+1 => -coefficient β m*(β-(m:ℝ))

def principalPart (β : ℝ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | m+1 => fun t => principalPart β m t+coefficient β m*phaseDerivative (β-m) t

def remainder (Φ : ℂ → ℂ) (β : ℝ) (m : ℕ) (t : ℂ) : ℂ :=
  Φ t-principalPart β m t

/-- Every finite integration-by-parts remainder has its exact derivative. -/
theorem remainder_hasDeriv {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ β C) (m : ℕ) {t : ℂ} (ht : t ∈ rightHalfPlane) :
    HasDerivAt (remainder Φ β m) (coefficient β m*phaseDerivative (β-m) t) t := by
  induction m with
  | zero =>
    have he : remainder Φ β 0 = Φ := by funext z; simp [remainder, principalPart]
    rw [he]
    simpa [coefficient] using hΦ.2 t ht
  | succ m ih =>
    have h := ih.sub ((phase_hasDeriv (β-m) ht).const_mul (coefficient β m))
    convert h using 1 <;> first
    | rfl
    | (funext z; simp only [remainder, principalPart, Pi.sub_apply]; ring)
    | (simp only [coefficient];
       have he : β-(m+1:ℕ) = β-(m:ℝ)-1 := by push_cast; ring
       rw [he]; push_cast; ring)

/-- A uniform quantitative terminal-remainder estimate, including the
actual integration constant. -/
theorem terminal_remainder_bound {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ β C) (m : ℕ) (hm : β-(m:ℝ) ≤ -2)
    {t : ℂ} (ht : t ∈ rightHalfPlane) (hρ : 1 ≤ ‖t‖) :
    ‖remainder Φ β m t‖ ≤
      (‖remainder Φ β m 1‖+2*‖coefficient β m‖*4^(-(β-m))*Real.exp 1)*Real.exp t.re := by
  have hd := negative_phase_displacement hm
    (fun z hz => remainder_hasDeriv hΦ m hz) ht hρ
  have hb : ‖remainder Φ β m t‖ ≤ ‖remainder Φ β m t-remainder Φ β m 1‖+‖remainder Φ β m 1‖ :=
    by
      have hh := norm_le_insert (remainder Φ β m 1) (remainder Φ β m t)
      simpa [norm_sub_rev, add_comm] using hh
  have hex : 1 ≤ Real.exp t.re := Real.one_le_exp_iff.mpr (le_of_lt ht)
  rw [Real.exp_add] at hd
  nlinarith [mul_le_mul_of_nonneg_left hex (norm_nonneg (remainder Φ β m 1))]


lemma phase_ratio_shift (β : ℝ) (m : ℕ) {t : ℂ} (ht : t ≠ 0) :
    phaseDerivative (β-m) t / phaseDerivative β t = t⁻¹^m := by
  induction m with
  | zero => simp [Complex.exp_ne_zero, phaseDerivative]
  | succ m ih =>
    have he : β-(m+1:ℕ) = (β-m)-1 := by push_cast; ring
    rw [he]
    have hh := phase_shift (β-m) ht
    have hs : phaseDerivative ((β-m)-1) t = phaseDerivative (β-m) t*t⁻¹ := by
      calc
        _ = (phaseDerivative ((β-m)-1) t*t)*t⁻¹ := by simp [mul_assoc, ht]
        _ = _ := by rw [hh]
    rw [hs, mul_div_right_comm, ih, pow_succ]

/-- The finite endpoint expansion has normalized limit 1 on the entire
right half-plane, not just on an a priori bounded horizontal strip. -/
theorem principalPart_ratio_limit {ι : Type*} {l : Filter ι} {t : ι → ℂ}
    (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hdom : ∀ᶠ x in l, t x ∈ rightHalfPlane) (β : ℝ) (m : ℕ) :
    Tendsto (fun x => principalPart β (m+1) (t x)/phaseDerivative β (t x)) l (𝓝 1) := by
  have hi : Tendsto (fun x => (t x)⁻¹) l (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp ht)
  induction m with
  | zero =>
    convert (tendsto_const_nhds : Tendsto (fun _ : ι => (1:ℂ)) l (𝓝 1)) using 1
    funext x
    simp [principalPart, coefficient, phaseDerivative, Complex.exp_ne_zero]
  | succ m ih =>
    have hq : Tendsto (fun x => coefficient β (m+1)*
        (phaseDerivative (β-(m+1)) (t x)/phaseDerivative β (t x))) l (𝓝 0) := by
      have hh := (tendsto_const_nhds (x := coefficient β (m+1))).mul (hi.pow (m+1))
      simp only [zero_pow (Nat.succ_ne_zero m), mul_zero] at hh
      apply hh.congr'
      filter_upwards [hdom] with x hx
      have he := phase_ratio_shift β (m+1) (Complex.slitPlane_ne_zero (Or.inl hx))
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun z => coefficient β (m+1)*z) he.symm
    have hh := ih.add hq
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [] with x
    simp only [principalPart, add_div, mul_div_assoc, Nat.cast_add, Nat.cast_one]

/-- The terminal remainder is negligible for every real beta > 0. -/
theorem remainder_ratio_limit {ι : Type*} {l : Filter ι} {t : ι → ℂ}
    {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C) (m : ℕ) (hm : β-(m:ℝ) ≤ -2)
    (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hdom : ∀ᶠ x in l, t x ∈ rightHalfPlane) :
    Tendsto (fun x => remainder Φ β m (t x)/phaseDerivative β (t x)) l (𝓝 0) := by
  let K := ‖remainder Φ β m 1‖+2*‖coefficient β m‖*4^(-(β-m))*Real.exp 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : ∀ᶠ x in l, ‖remainder Φ β m (t x)/phaseDerivative β (t x)‖ ≤ K/‖t x‖^β := by
    filter_upwards [ht.eventually_ge_atTop 1, hdom] with x hρ hx
    have hp : 0 < ‖t x‖ := by linarith
    have hn : t x ≠ 0 := norm_pos_iff.mp hp
    rw [norm_div]
    change ‖remainder Φ β m (t x)‖ /
      ‖ZeroDensity.PhaseDerivativeBounds.phaseDerivative (β:ℂ) (t x)‖ ≤ _
    rw [ZeroDensity.PhaseDerivativeBounds.norm_phaseDerivative β hn]
    have hb := terminal_remainder_bound hΦ m hm hx hρ
    change ‖remainder Φ β m (t x)‖ ≤ K*Real.exp (t x).re at hb
    calc
      _ ≤ (K*Real.exp (t x).re)/(‖t x‖^β*Real.exp (t x).re) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by field_simp [ne_of_gt (Real.exp_pos (t x).re)]
  exact squeeze_zero_norm' hb (tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hβ).comp ht))

/-- Actual primitive asymptotic for arbitrary real beta > 0, uniformly in
the right half-plane as |t| tends to infinity. -/
theorem primitive_ratio_limit {ι : Type*} {l : Filter ι} {t : ι → ℂ}
    {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C)
    (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hdom : ∀ᶠ x in l, t x ∈ rightHalfPlane) :
    Tendsto (fun x => Φ (t x)/phaseDerivative β (t x)) l (𝓝 1) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (β+2)
  have hn : β-((m+1:ℕ):ℝ) ≤ -2 := by push_cast; linarith
  have hh := (remainder_ratio_limit hβ hΦ (m+1) hn ht hdom).add
    (principalPart_ratio_limit ht hdom β m)
  simp only [zero_add] at hh
  convert hh using 1
  funext x
  dsimp only [remainder]
  ring

end ZeroDensity.PhasePrimitiveRemainder
