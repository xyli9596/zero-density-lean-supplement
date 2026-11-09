import ZeroDensity.MainTheorem
import ZeroDensity.SectorGeometry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Primitive uniqueness and fixed logarithmic winding for actual analytic
branches. These do not assume an inverse asymptotic formula. The general
β>0 integration-by-parts estimate is not proved in this module. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.InverseBranchFoundations
open ZeroDensity.MainTheorem

theorem rightHalfPlane_open : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem rightHalfPlane_preconnected : IsPreconnected rightHalfPlane :=
  ((convex_Ioi (0:ℝ)).linear_preimage Complex.reLm).isPreconnected

/-- The β=0 primitive with arbitrary integration constant is exactly known.
This separately handles the case where q need not tend to infinity on
vertical right-half-plane sequences. -/
theorem zero_beta_primitive {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ 0 C) :
    ∀ t ∈ rightHalfPlane, Φ t = Complex.exp t + C - Complex.exp 1 := by
  let G : ℂ → ℂ := fun t => Complex.exp t+C-Complex.exp 1
  have hd (t : ℂ) (ht : t ∈ rightHalfPlane) : HasDerivAt Φ (Complex.exp t) t := by
    simpa [phaseDerivative] using hΦ.2 t ht
  have hg (t : ℂ) : HasDerivAt G (Complex.exp t) t := by
    simpa [G] using ((Complex.hasDerivAt_exp t).add_const C).sub_const (Complex.exp 1)
  have he : EqOn Φ G rightHalfPlane := rightHalfPlane_open.eqOn_of_deriv_eq
    rightHalfPlane_preconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t ht).deriv,(hg t).deriv])
    (show (1:ℂ) ∈ rightHalfPlane by norm_num [rightHalfPlane])
    (by simp [G,hΦ.1])
  exact he

/-- Equality of actual exponentials on a connected open analytic domain
forces a single integer winding index on the entire domain. -/
theorem fixed_integer_winding {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsPreconnected U) {A B : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hexp : ∀ z ∈ U, Complex.exp (A z) = Complex.exp (B z))
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    ∃ k : ℤ, ∀ z ∈ U, A z = B z+(k:ℂ)*(2*Real.pi*Complex.I) := by
  have hder : EqOn (deriv A) (deriv B) U := by
    intro z hz
    have ha := (hA z hz).differentiableAt.hasDerivAt
    have hb := (hB z hz).differentiableAt.hasDerivAt
    have hca := (Complex.hasDerivAt_exp (A z)).comp z ha
    have hcb := (Complex.hasDerivAt_exp (B z)).comp z hb
    have heq : (fun w => Complex.exp (A w)) =ᶠ[𝓝 z] (fun w => Complex.exp (B w)) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact hexp w hw
    have hh := hca.unique (hcb.congr_of_eventuallyEq heq)
    rw [hexp z hz] at hh
    exact mul_left_cancel₀ (Complex.exp_ne_zero (B z)) hh
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hexp z₀ hz₀)
  refine ⟨k, ?_⟩
  have he := hU.eqOn_of_deriv_eq hconn
    (fun z hz => (hA z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (((hB z hz).differentiableAt.hasDerivAt).add_const
      ((k:ℂ)*(2*Real.pi*Complex.I))).differentiableAt.differentiableWithinAt)
    (fun z hz => by rw [deriv_add_const]; exact hder hz)
    hz₀ hk
  exact he

/-- The integration constant causes a uniformly vanishing logarithmic
correction on every set of rays, independently of the angular range. -/
theorem logarithmic_constant_correction {ι : Type*} (D : Set ι)
    (θ : ι → ℝ) (K : ℂ) :
    TendstoUniformlyOn (fun (R : ℝ) i => Complex.log
      (1-K/((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))) (fun _ => 0) atTop D := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : ContinuousAt Complex.log (1:ℂ) :=
    (analyticAt_clog (by simp : (1:ℂ) ∈ Complex.slitPlane)).continuousAt
  obtain ⟨δ,hδ,hd⟩ := Metric.continuousAt_iff.mp hc ε hε
  have ht : Tendsto (fun R : ℝ => ‖K‖/R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_gt_atTop (0:ℝ), ht.eventually (gt_mem_nhds hδ)] with R hR hh
  intro i hi
  have hnorm : ‖(R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)‖ = R := by
    simp [norm_mul,Complex.norm_exp,abs_of_pos hR]
  have hdist : dist (1-K/((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I))) 1 < δ := by
    rw [dist_eq_norm]
    have he : (1-K/((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))-1 =
      -(K/((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I))) := by ring
    rw [he,norm_neg,norm_div,hnorm]
    exact hh
  simpa [dist_comm] using hd hdist

/-- Exact exponential relation for every actual β=0 inverse branch. -/
theorem zero_beta_inverse_exponential {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ 0 C) (B : InverseBranch Φ)
    {s : ℂ} (hs : s ∈ ZeroDensity.CountGeometry.angularSector B.S₀ B.left B.right) :
    Complex.exp (B.ψ s) = s-(C-Complex.exp 1) := by
  have hp := zero_beta_primitive hΦ (B.ψ s) (B.image_right hs)
  have hi := B.right_inverse s hs
  rw [hi] at hp
  linear_combination -hp

/-- The β=0 logarithmic branch formula is derived from the actual inverse
relation. The only logarithm input is an analytic chosen logarithm of s;
no inverse formula, branch index, or asymptotic is assumed. -/
theorem zero_beta_branch_log_formula {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ 0 C) (B : InverseBranch Φ)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hsub : U ⊆ ZeroDensity.CountGeometry.angularSector B.S₀ B.left B.right)
    (hlarge : ∀ s ∈ U, ‖C-Complex.exp 1‖ < ‖s‖)
    (L : ℂ → ℂ) (hL : AnalyticOnNhd ℂ L U)
    (hexpL : ∀ s ∈ U, Complex.exp (L s) = s)
    {s₀ : ℂ} (hs₀ : s₀ ∈ U) :
    ∃ k : ℤ, ∀ s ∈ U, B.ψ s = L s+
      Complex.log (1-(C-Complex.exp 1)/s)+(k:ℂ)*(2*Real.pi*Complex.I) := by
  let K := C-Complex.exp 1
  have hsn (s : ℂ) (hs : s ∈ U) : s ≠ 0 := by
    have hh : 0 < ‖s‖ := (norm_nonneg K).trans_lt (hlarge s hs)
    exact norm_pos_iff.mp hh
  have hslit (s : ℂ) (hs : s ∈ U) : 1-K/s ∈ Complex.slitPlane := by
    have hh : ‖-(K/s)‖ < 1 := by
      rw [norm_neg,norm_div]
      exact (div_lt_one (norm_pos_iff.mpr (hsn s hs))).mpr (hlarge s hs)
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh
  have hcorr : AnalyticOnNhd ℂ (fun s => Complex.log (1-K/s)) U := by
    intro s hs
    exact ((analyticAt_const.sub (analyticAt_const.div analyticAt_id (hsn s hs))).clog (hslit s hs))
  have he : ∀ s ∈ U, Complex.exp (B.ψ s) =
      Complex.exp (L s+Complex.log (1-K/s)) := by
    intro s hs
    rw [Complex.exp_add,hexpL s hs,Complex.exp_log (Complex.slitPlane_ne_zero (hslit s hs))]
    have hh := zero_beta_inverse_exponential hΦ B (hsub hs)
    dsimp [K]
    rw [hh]
    field_simp [hsn s hs]
    <;> ring
  exact fixed_integer_winding hU hconn (B.analytic.mono hsub) (hL.add hcorr) he hs₀

/-- Uniform β=0 inverse expansion on rays is derived from the actual
primitive and right inverse. Inputs describing L are merely the chosen
holomorphic argument; the inverse formula itself is not an input. -/
theorem zero_beta_inverse_uniform {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ 0 C) (B : InverseBranch Φ)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hsub : U ⊆ ZeroDensity.CountGeometry.angularSector B.S₀ B.left B.right)
    (hlarge : ∀ s ∈ U, ‖C-Complex.exp 1‖ < ‖s‖)
    (L : ℂ → ℂ) (hL : AnalyticOnNhd ℂ L U)
    (hexpL : ∀ s ∈ U, Complex.exp (L s) = s)
    {s₀ : ℂ} (hs₀ : s₀ ∈ U)
    {ι : Type*} (D : Set ι) (θ : ι → ℝ) (T : ℝ)
    (hrays : ∀ R ≥ T, ∀ i ∈ D,
      (R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I) ∈ U)
    (hlog : ∀ R ≥ T, ∀ i ∈ D,
      L ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)) =
        (Real.log R:ℂ)+(θ i:ℂ)*Complex.I) :
    ∃ k : ℤ, TendstoUniformlyOn (fun (R : ℝ) i =>
      B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)) -
        ((Real.log R:ℂ)+(θ i:ℂ)*Complex.I+(k:ℂ)*(2*Real.pi*Complex.I)))
      (fun _ => 0) atTop D := by
  obtain ⟨k,hk⟩ := zero_beta_branch_log_formula hΦ B hU hconn hsub hlarge L hL hexpL hs₀
  refine ⟨k, ?_⟩
  have hc := logarithmic_constant_correction D θ (C-Complex.exp 1)
  rw [Metric.tendstoUniformlyOn_iff] at hc ⊢
  intro ε hε
  filter_upwards [eventually_ge_atTop T,hc ε hε] with R hR he
  intro i hi
  rw [hk _ (hrays R hR i hi),hlog R hR i hi]
  have hid : (Real.log R:ℂ)+(θ i:ℂ)*Complex.I+
      Complex.log (1-(C-Complex.exp 1)/((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))+
      (k:ℂ)*(2*Real.pi*Complex.I) -
      ((Real.log R:ℂ)+(θ i:ℂ)*Complex.I+(k:ℂ)*(2*Real.pi*Complex.I)) =
      Complex.log (1-(C-Complex.exp 1)/((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I))) := by ring
  rw [hid]
  exact he i hi

/-- Actual β=0 inverse branches escape every bounded t-disk uniformly
on rays. This uses only the primitive and inverse identity. -/
theorem zero_beta_inverse_escape {Φ : ℂ → ℂ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ 0 C) (B : InverseBranch Φ)
    {ι : Type*} (D : Set ι) (θ : ι → ℝ)
    (hθ : ∀ i ∈ D, θ i ∈ Ioo B.left B.right) :
    ∀ M : ℝ, ∀ᶠ R : ℝ in atTop, ∀ i ∈ D,
      M < ‖B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I))‖ := by
  intro M
  filter_upwards [eventually_ge_atTop
    (max (B.S₀+1) (Real.exp M+‖C-Complex.exp 1‖+1))] with R hR
  intro i hi
  have hRp : 0 < R := by have := (le_max_left _ _).trans hR; linarith [B.radius_pos]
  have hs : (R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I) ∈
      ZeroDensity.CountGeometry.angularSector B.S₀ B.left B.right := by
    exact ⟨R,by have := (le_max_left _ _).trans hR; linarith,θ i,hθ i hi,rfl⟩
  have he := zero_beta_inverse_exponential hΦ B hs
  have hn : ‖(R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)‖ = R := by
    simp [Complex.norm_exp,abs_of_pos hRp]
  by_contra hsmall
  have hsmall' : ‖B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I))‖ ≤ M := le_of_not_gt hsmall
  have hre : (B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I))).re ≤ M :=
    (Complex.re_le_norm _).trans hsmall'
  have hex : ‖Complex.exp (B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))‖ ≤ Real.exp M := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hre
  have hid : (R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I) =
      Complex.exp (B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))+(C-Complex.exp 1) := by
    rw [he]; ring
  have hbound : R ≤ Real.exp M+‖C-Complex.exp 1‖ := by
    calc
      R = ‖(R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)‖ := hn.symm
      _ = ‖Complex.exp (B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))+(C-Complex.exp 1)‖ := congrArg norm hid
      _ ≤ ‖Complex.exp (B.ψ ((R:ℂ)*Complex.exp ((θ i:ℂ)*Complex.I)))‖+‖C-Complex.exp 1‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left hex _
  have hh := (le_max_right _ _).trans hR
  linarith

/-- Exact inverse derivative obtained from the actual phase primitive and
actual inverse identity, without an inverse derivative assumption. -/
theorem inverse_hasDeriv {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ}
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {s : ℂ} (hs : s ∈ ZeroDensity.CountGeometry.angularSector B.S₀ B.left B.right) :
    HasDerivAt B.ψ (phaseDerivative β (B.ψ s))⁻¹ s := by
  have hp := hΦ.2 (B.ψ s) (B.image_right hs)
  have hψ := (B.analytic s hs).differentiableAt.hasDerivAt
  have hc := hp.comp s hψ
  have heq : (fun w => Φ (B.ψ w)) =ᶠ[𝓝 s] (fun w => w) := by
    filter_upwards [(ZeroDensity.SectorGeometry.sector_open B.radius_pos).mem_nhds hs] with w hw
    exact B.right_inverse w hw
  have hi : HasDerivAt (fun w => Φ (B.ψ w)) 1 s :=
    (hasDerivAt_id s).congr_of_eventuallyEq heq
  have he : phaseDerivative β (B.ψ s)*deriv B.ψ s = 1 := hc.unique hi
  have hqn : phaseDerivative β (B.ψ s) ≠ 0 := Complex.exp_ne_zero _
  have hd : deriv B.ψ s = (phaseDerivative β (B.ψ s))⁻¹ := by
    calc
      _ = (phaseDerivative β (B.ψ s))⁻¹ *
          (phaseDerivative β (B.ψ s)*deriv B.ψ s) := by rw [←mul_assoc,inv_mul_cancel₀ hqn,one_mul]
      _ = _ := by rw [he,mul_one]
  rw [hd] at hψ
  exact hψ

#print axioms inverse_hasDeriv
#print axioms zero_beta_inverse_escape
#print axioms zero_beta_inverse_uniform
#print axioms zero_beta_branch_log_formula
#print axioms logarithmic_constant_correction
#print axioms zero_beta_primitive
#print axioms fixed_integer_winding
end ZeroDensity.InverseBranchFoundations
