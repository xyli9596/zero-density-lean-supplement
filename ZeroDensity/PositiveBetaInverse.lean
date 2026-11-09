import ZeroDensity.PhasePrimitiveRemainder
import ZeroDensity.LogarithmicInversion
import ZeroDensity.SectorLogarithm
import ZeroDensity.InverseGeometry
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Positive-beta inverse estimates for an actual primitive and its actual
holomorphic inverse branch. Intermediate lemmas use arbitrary filters so that
closed-subsector uniformity can be obtained by a product filter. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.PositiveBetaInverse
open ZeroDensity.MainTheorem ZeroDensity.InverseBranchFoundations
open ZeroDensity.CountGeometry ZeroDensity.PhasePrimitiveRemainder

/-- An actual primitive is bounded on bounded portions of the right half-plane,
even though the imaginary axis is not included in its domain. -/
theorem primitive_ball_bound {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 ≤ β)
    (hΦ : IsPhasePrimitive Φ β C) {M : ℝ} (hM : 1 ≤ M)
    {t : ℂ} (ht : t ∈ rightHalfPlane) (hn : ‖t‖ ≤ M) :
    ‖Φ t‖ ≤ ‖C‖+M^β*Real.exp M*(M+1) := by
  let U : Set ℂ := rightHalfPlane ∩ Metric.closedBall 0 M
  have hU : Convex ℝ U :=
    ((convex_Ioi (0:ℝ)).linear_preimage Complex.reLm).inter (convex_closedBall 0 M)
  have hq (z : ℂ) (hz : z ∈ U) : ‖phaseDerivative β z‖ ≤ M^β*Real.exp M := by
    have hzn : z ≠ 0 := Complex.slitPlane_ne_zero (Or.inl hz.1)
    have hnorm : ‖z‖ ≤ M := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2
    change ‖ZeroDensity.PhaseDerivativeBounds.phaseDerivative (β:ℂ) z‖ ≤ _
    rw [ZeroDensity.PhaseDerivativeBounds.norm_phaseDerivative β hzn]
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg z) hnorm hβ)
      (Real.exp_le_exp.mpr ((Complex.re_le_norm z).trans hnorm))
      (Real.exp_pos _).le (by positivity)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hΦ.2 z hz.1).hasDerivWithinAt) hq hU
    (show (1:ℂ) ∈ U by simp [U, rightHalfPlane, Metric.mem_closedBall, dist_eq_norm, hM])
    (show t ∈ U by simpa [U, Metric.mem_closedBall, dist_eq_norm] using And.intro ht hn)
  rw [hΦ.1] at hb
  have hlen : ‖t-1‖ ≤ M+1 := by
    have h := norm_sub_le t (1:ℂ)
    simp only [norm_one] at h
    linarith
  have hh := norm_le_insert C (Φ t)
  rw [norm_sub_rev] at hh
  have hK : 0 ≤ M^β*Real.exp M := by positivity
  exact hh.trans (add_le_add_right (hb.trans (mul_le_mul_of_nonneg_left hlen hK)) _)

/-- Escape is forced by the actual inverse identity; it is not an input
asymptotic condition on the branch. -/
theorem inverse_escape {ι : Type*} {l : Filter ι} {s : ι → ℂ}
    {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 ≤ β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    (hs : ∀ᶠ x in l, s x ∈ angularSector B.S₀ B.left B.right)
    (hn : Tendsto (fun x => ‖s x‖) l atTop) :
    Tendsto (fun x => ‖B.ψ (s x)‖) l atTop := by
  apply tendsto_atTop.2
  intro M
  let N := max 1 M
  have hN : 1 ≤ N := le_max_left _ _
  let K := ‖C‖+N^β*Real.exp N*(N+1)
  filter_upwards [hs, hn.eventually_gt_atTop K] with x hx hlarge
  by_contra hsmall
  have hbound : ‖B.ψ (s x)‖ ≤ N :=
    (le_of_not_ge hsmall).trans (le_max_right _ _)
  have hb := primitive_ball_bound hβ hΦ hN (B.image_right hx) hbound
  rw [B.right_inverse _ hx] at hb
  exact not_le_of_gt hlarge hb

lemma uniform_zero_iff {ι : Type*} {F : ℝ → ι → ℂ} {D : Set ι} :
    TendstoUniformlyOn F (fun _ => 0) atTop D ↔
    Tendsto (fun x : ℝ × ι => F x.1 x.2) (atTop ×ˢ 𝓟 D) (𝓝 0) := by
  rw [Metric.tendstoUniformlyOn_iff, Metric.tendsto_nhds]
  simp only [eventually_prod_principal_iff, dist_comm]

lemma ray_norm (R θ : ℝ) (hR : 0 ≤ R) :
    ‖(R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)‖ = R := by
  simp [Complex.norm_exp, abs_of_nonneg hR]

lemma rays_domain {Φ : ℂ → ℂ} (B : InverseBranch Φ) {D : Set ℝ} (hD : D ⊆ Ioo B.left B.right) :
    ∀ᶠ x : ℝ × ℝ in atTop ×ˢ 𝓟 D,
      (x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I) ∈ angularSector B.S₀ B.left B.right := by
  rw [eventually_prod_principal_iff]
  filter_upwards [eventually_gt_atTop B.S₀] with R hR
  intro θ hθ
  exact ⟨R,hR,θ,hD hθ,rfl⟩

lemma rays_norm_limit (D : Set ℝ) :
    Tendsto (fun x : ℝ × ℝ => ‖(x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I)‖)
      (atTop ×ˢ 𝓟 D) atTop := by
  apply (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ 𝓟 D) atTop).congr'
  change ∀ᶠ x : ℝ × ℝ in atTop ×ˢ 𝓟 D, x.1 = _
  rw [eventually_prod_principal_iff]
  filter_upwards [eventually_ge_atTop (0:ℝ)] with R hR
  intro θ hθ
  exact (ray_norm R θ hR).symm

/-- The actual forward equation gives a ratio tending uniformly to 1. -/
theorem inverse_ratio_limit {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {D : Set ℝ} (hD : D ⊆ Ioo B.left B.right) :
    Tendsto (fun x : ℝ × ℝ =>
      ((x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I))/
        phaseDerivative β (B.ψ ((x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I))))
      (atTop ×ˢ 𝓟 D) (𝓝 1) := by
  have hs := rays_domain B hD
  have he := inverse_escape hβ.le hΦ B hs (rays_norm_limit D)
  have hp := primitive_ratio_limit hβ hΦ he (hs.mono (fun x hx => B.image_right hx))
  apply hp.congr'
  filter_upwards [hs] with x hx
  rw [B.right_inverse _ hx]

/-- Uniform logarithmic error of the actual forward equation on inverse rays. -/
theorem inverse_log_correction {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {D : Set ℝ} (hD : D ⊆ Ioo B.left B.right) :
    Tendsto (fun x : ℝ × ℝ => Complex.log
      (((x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I))/
        phaseDerivative β (B.ψ ((x.1:ℂ)*Complex.exp ((x.2:ℂ)*Complex.I)))))
      (atTop ×ˢ 𝓟 D) (𝓝 0) := by
  have hc : ContinuousAt Complex.log (1:ℂ) :=
    (analyticAt_clog (by simp : (1:ℂ) ∈ Complex.slitPlane)).continuousAt
  convert hc.tendsto.comp (inverse_ratio_limit hβ hΦ B hD) using 1 <;>
    first | rfl | simp [Complex.log_one, Function.comp_def]

/-- An exact logarithmic equation with one integer for the whole connected
sector. Its error is computed from the actual inverse, not supplied. -/
theorem branch_log_equation {Φ : ℂ → ℂ} {β : ℝ} (B : InverseBranch Φ)
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hsub : U ⊆ angularSector B.S₀ B.left B.right)
    (hslit : ∀ s ∈ U, s/phaseDerivative β (B.ψ s) ∈ Complex.slitPlane)
    (L : ℂ → ℂ) (hL : AnalyticOnNhd ℂ L U)
    (hexpL : ∀ s ∈ U, Complex.exp (L s) = s)
    {s₀ : ℂ} (hs₀ : s₀ ∈ U) :
    ∃ k : ℤ, ∀ s ∈ U,
      B.ψ s+(β:ℂ)*Complex.log (B.ψ s)+Complex.log (s/phaseDerivative β (B.ψ s)) =
        L s+(k:ℂ)*(2*Real.pi*Complex.I) := by
  have hp (s : ℂ) (hs : s ∈ U) : B.ψ s ∈ Complex.slitPlane := Or.inl (B.image_right (hsub hs))
  have hlogψ : AnalyticOnNhd ℂ (fun s => Complex.log (B.ψ s)) U :=
    fun s hs => (B.analytic s (hsub hs)).clog (hp s hs)
  have hq : AnalyticOnNhd ℂ (fun s => phaseDerivative β (B.ψ s)) U := by
    intro s hs
    exact (ZeroDensity.PhaseDerivativeBounds.phaseDerivative_analytic (β:ℂ) (hp s hs)).comp
      (B.analytic s (hsub hs))
  have hcorr : AnalyticOnNhd ℂ (fun s => Complex.log (s/phaseDerivative β (B.ψ s))) U := by
    intro s hs
    exact (analyticAt_id.div (hq s hs) (Complex.exp_ne_zero _)).clog (hslit s hs)
  have ha : AnalyticOnNhd ℂ (fun s => B.ψ s+(β:ℂ)*Complex.log (B.ψ s)+
      Complex.log (s/phaseDerivative β (B.ψ s))) U :=
    ((B.analytic.mono hsub).add (analyticOnNhd_const.mul hlogψ)).add hcorr
  apply fixed_integer_winding hU hconn ha hL ?_ hs₀
  intro s hs
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hslit s hs)), hexpL s hs]
  have he : Complex.exp (B.ψ s+(β:ℂ)*Complex.log (B.ψ s)) = phaseDerivative β (B.ψ s) := by
    unfold phaseDerivative
    congr 1
    ring
  rw [he]
  exact mul_div_cancel₀ s (Complex.exp_ne_zero _)

/-- On a sufficiently far tail of the actual sector the computed ratio
lies in the principal logarithm domain, so one fixed branch index exists. -/
theorem tail_log_equation {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ) :
    ∃ S : ℝ, B.S₀ < S ∧ ∃ k : ℤ, ∀ s ∈ angularSector S B.left B.right,
      B.ψ s+(β:ℂ)*Complex.log (B.ψ s)+Complex.log (s/phaseDerivative β (B.ψ s)) =
        ZeroDensity.SectorLogarithm.chosenLog ((B.left+B.right)/2) s+
          (k:ℂ)*(2*Real.pi*Complex.I) := by
  have hr := inverse_ratio_limit hβ hΦ B (Subset.rfl : Ioo B.left B.right ⊆ Ioo B.left B.right)
  have hh := (Metric.tendsto_nhds.mp hr) (1/2) (by norm_num)
  rw [eventually_prod_principal_iff] at hh
  obtain ⟨N,hN⟩ := eventually_atTop.mp hh
  let S := max (B.S₀+1) N
  have hSB : B.S₀ < S := by dsimp [S]; linarith [le_max_left (B.S₀+1) N]
  have hS : 0 < S := B.radius_pos.trans hSB
  let U := angularSector S B.left B.right
  have hsub : U ⊆ angularSector B.S₀ B.left B.right := by
    rintro s ⟨R,hR,θ,hθ,hs⟩
    exact ⟨R,hSB.trans hR,θ,hθ,hs⟩
  have hslit : ∀ s ∈ U, s/phaseDerivative β (B.ψ s) ∈ Complex.slitPlane := by
    rintro s ⟨R,hR,θ,hθ,rfl⟩
    have hRN : N ≤ R := (le_max_right _ _).trans hR.le
    have hb := hN R hRN θ hθ
    rw [dist_eq_norm] at hb
    have he := Complex.mem_slitPlane_of_norm_lt_one (hb.trans (by norm_num : (1/2:ℝ) < 1))
    simpa only [add_sub_cancel] using he
  let φ := (B.left+B.right)/2
  let s₀ := ((S+1:ℝ):ℂ)*Complex.exp ((φ:ℂ)*Complex.I)
  have hs₀ : s₀ ∈ U := by
    refine ⟨S+1,by linarith,φ,?_,rfl⟩
    dsimp [φ]; constructor <;> linarith [B.left_lt_right]
  have hexp : ∀ s ∈ U, Complex.exp (ZeroDensity.SectorLogarithm.chosenLog φ s) = s := by
    rintro s ⟨R,hR,θ,hθ,rfl⟩
    apply ZeroDensity.SectorLogarithm.exp_chosenLog
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hS.trans hR))) (Complex.exp_ne_zero _)
  obtain ⟨k,hk⟩ := branch_log_equation B
    (ZeroDensity.SectorGeometry.sector_open hS) (ZeroDensity.SectorGeometry.sector_preconnected hS)
    hsub hslit (ZeroDensity.SectorLogarithm.chosenLog φ)
    (ZeroDensity.SectorLogarithm.chosenLog_analytic hS B.opening_lt_two_pi) hexp hs₀
  exact ⟨S,hSB,k,hk⟩

/-- Complete complex-log inverse asymptotic, uniform on each closed angular
interval strictly inside the actual branch sector. -/
theorem inverse_complex_uniform_closed {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    ∃ k : ℤ, TendstoUniformlyOn (fun (R θ : ℝ) =>
      B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) -
        (((Real.log R:ℂ)+(θ:ℂ)*Complex.I) -
          (β:ℂ)*Complex.log ((Real.log R:ℂ)+(θ:ℂ)*Complex.I) +
          (k:ℂ)*(2*Real.pi*Complex.I))) (fun _ => 0) atTop (Icc a b) := by
  obtain ⟨S,hSB,k,hk⟩ := tail_log_equation hβ hΦ B
  have hD : Icc a b ⊆ Ioo B.left B.right :=
    fun θ hθ => ⟨hleft.trans_le hθ.1,lt_of_le_of_lt hθ.2 hright⟩
  have hs := rays_domain B hD
  have ht := inverse_escape hβ.le hΦ B hs (rays_norm_limit (Icc a b))
  have he := inverse_log_correction hβ hΦ B hD
  refine ⟨k, uniform_zero_iff.mpr ?_⟩
  apply ZeroDensity.LogarithmicInversion.invert_log_equation β
    ((k:ℂ)*(2*Real.pi*Complex.I)) ht ?_ he ?_
  · rw [eventually_prod_principal_iff]
    filter_upwards [eventually_gt_atTop (1:ℝ)] with R hR
    intro θ hθ
    simpa using Real.log_pos hR
  · rw [eventually_prod_principal_iff]
    filter_upwards [eventually_gt_atTop (max S 1)] with R hR
    intro θ hθ
    have hRS : S < R := (le_max_left _ _).trans_lt hR
    have hRpos : 0 < R := by have := (le_max_right _ _).trans_lt hR; linarith
    have heq := hk _ ⟨R,hRS,θ,hD hθ,rfl⟩
    rw [ZeroDensity.SectorLogarithm.chosenLog_ray hRpos] at heq
    · exact heq
    · linarith [hθ.1,B.opening_lt_two_pi]
    · linarith [hθ.2,B.opening_lt_two_pi]

/-- The complex logarithm of log R + i theta differs from log log R by o(1),
uniformly for theta in an arbitrary bounded interval. -/
theorem log_rectangular_limit (a b : ℝ) :
    Tendsto (fun x : ℝ × ℝ =>
      Complex.log ((Real.log x.1:ℂ)+(x.2:ℂ)*Complex.I)-(Real.log (Real.log x.1):ℂ))
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
  let L : ℝ × ℝ → ℂ := fun x => (Real.log x.1:ℂ)+(x.2:ℂ)*Complex.I
  let X : ℝ × ℝ → ℂ := fun x => (Real.log x.1:ℂ)
  have hx : Tendsto (fun x : ℝ × ℝ => Real.log x.1) (atTop ×ˢ 𝓟 (Icc a b)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_fst
  let A : ℝ := max |a| |b|
  have hA : ∀ θ ∈ Icc a b, |θ| ≤ A := by
    intro θ hθ
    exact abs_le.mpr ⟨by have := le_max_left |a| |b|; have := neg_abs_le a; linarith [hθ.1],
      by have := le_max_right |a| |b|; have := le_abs_self b; linarith [hθ.2]⟩
  have hy : Tendsto (fun x : ℝ × ℝ => (x.2:ℂ)*Complex.I/X x)
      (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop hx :
      Tendsto (fun x => A/Real.log x.1) _ (𝓝 0))
    rw [eventually_prod_principal_iff]
    filter_upwards [eventually_gt_atTop (1:ℝ)] with R hR
    intro θ hθ
    have hlog : 0 < Real.log R := Real.log_pos hR
    simp only [X, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (hA θ hθ) hlog.le
  have hratio : Tendsto (fun x => L x/X x) (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1:ℂ))).add hy
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hx.eventually_gt_atTop 0] with x hx
    dsimp only [L,X]
    rw [add_div, div_self (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
  have hc : ContinuousAt Complex.log (1:ℂ) :=
    (analyticAt_clog (by simp : (1:ℂ) ∈ Complex.slitPlane)).continuousAt
  have hlog : Tendsto (fun x => Complex.log (L x/X x)) (atTop ×ˢ 𝓟 (Icc a b)) (𝓝 0) := by
    convert hc.tendsto.comp hratio using 1 <;> first | rfl | simp
  apply hlog.congr'
  filter_upwards [hx.eventually_gt_atTop 0] with x hx
  have hLn : X x ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hre : 0 < (L x/X x).re := by
    dsimp only [L,X]
    rw [add_div, div_self hLn]
    simp
  have he := ZeroDensity.LogarithmicInversion.log_difference_of_right_ratio
    (show 0 < (X x).re by simpa [X] using hx) hre
  rw [←Complex.ofReal_log hx.le] at he
  exact he.symm

/-- The manuscript's rectangular expansion, from the actual primitive and
actual branch alone. The integer is fixed on the connected branch sector. -/
theorem inverse_uniform_closed {Φ : ℂ → ℂ} {β : ℝ} {C : ℂ} (hβ : 0 < β)
    (hΦ : IsPhasePrimitive Φ β C) (B : InverseBranch Φ)
    {a b : ℝ} (hleft : B.left < a) (hab : a ≤ b) (hright : b < B.right) :
    ∃ k : ℤ, TendstoUniformlyOn (fun (R θ : ℝ) =>
      B.ψ ((R:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)) -
        (((Real.log R-β*Real.log (Real.log R):ℝ):ℂ)+
          ((θ+2*Real.pi*k:ℝ):ℂ)*Complex.I)) (fun _ => 0) atTop (Icc a b) := by
  obtain ⟨k,hk⟩ := inverse_complex_uniform_closed hβ hΦ B hleft hab hright
  refine ⟨k, uniform_zero_iff.mpr ?_⟩
  have he := uniform_zero_iff.mp hk
  have hl := log_rectangular_limit a b
  have hc := (tendsto_const_nhds (x := (β:ℂ))).mul hl
  have hh := he.sub hc
  simp only [mul_zero, sub_zero] at hh
  convert hh using 1 <;> first | rfl | (funext x; push_cast; ring)

#print axioms inverse_uniform_closed
end ZeroDensity.PositiveBetaInverse
