import ZeroDensity.ExactChange
import ZeroDensity.PhaseCoefficientLimits
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

namespace ZeroDensity.PhaseDerivativeBounds
open Filter Polynomial Asymptotics
open scoped Topology
noncomputable section

/-- Actual phase derivative on the principal logarithm branch. -/
def phaseDerivative (β : ℂ) (z : ℂ) : ℂ := Complex.exp (β * Complex.log z + z)

lemma phaseDerivative_ne_zero (β z : ℂ) : phaseDerivative β z ≠ 0 := Complex.exp_ne_zero _

lemma phaseDerivative_analytic (β : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (phaseDerivative β) z := by
  exact ((analyticAt_const.mul (analyticAt_clog hz)).add analyticAt_id).cexp

lemma phaseDerivative_hasDeriv (β : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (phaseDerivative β) (phaseDerivative β z * (1 + β * z⁻¹)) z := by
  have h := (((Complex.hasDerivAt_log hz).const_mul β).add (hasDerivAt_id z)).cexp
  convert h using 1 <;> first | rfl | (simp only [phaseDerivative, Pi.add_apply, id_eq]; ring)

lemma phaseDerivative_deriv (β : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    deriv (phaseDerivative β) z = phaseDerivative β z * (1 + β * z⁻¹) :=
  (phaseDerivative_hasDeriv β hz).deriv

/-- Explicit polynomial recurrence for every actual chain coefficient. -/
def chainPolynomial (β : ℂ) : ℕ → ℕ → Polynomial ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => -X ^ 2 * (chainPolynomial β m 0).derivative
  | m + 1, k + 1 =>
      C (k + 1 : ℂ) * (1 + C β * X) * chainPolynomial β m (k + 1) -
        X ^ 2 * (chainPolynomial β m (k + 1)).derivative + chainPolynomial β m k

lemma polynomial_product_hasDeriv (β : ℂ) {z : ℂ} (hz : z ∈ Complex.slitPlane)
    (k : ℕ) (P : Polynomial ℂ) :
    HasDerivAt (fun t => phaseDerivative β t ^ k * P.eval t⁻¹)
      (phaseDerivative β z ^ k *
        ((k : ℂ) * (1 + β * z⁻¹) * P.eval z⁻¹ - z⁻¹ ^ 2 * P.derivative.eval z⁻¹)) z := by
  have hi := hasDerivAt_inv (Complex.slitPlane_ne_zero hz)
  have hp := (P.hasDerivAt z⁻¹).comp z hi
  have hq := (phaseDerivative_hasDeriv β hz).pow k
  have hm := hq.mul hp
  convert hm using 1 <;> first
  | rfl
  | (simp only [Function.comp_apply, Pi.pow_apply, inv_pow];
      cases k with
      | zero => simp [mul_comm]
      | succ k => simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]; ring)

/-- All chain coefficients are a power of the actual phase derivative times an
explicit polynomial in `1/z`, proved from the actual derivative recurrence. -/
theorem chainCoeff_polynomial (β : ℂ) (m k : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ExactChange.chainCoeff (phaseDerivative β) m k z =
      phaseDerivative β z ^ k * (chainPolynomial β m k).eval z⁻¹ := by
  induction m generalizing k z with
  | zero => cases k <;> simp [ExactChange.chainCoeff, chainPolynomial]
  | succ m ih =>
    have heq (j : ℕ) : ExactChange.chainCoeff (phaseDerivative β) m j =ᶠ[𝓝 z]
        (fun t => phaseDerivative β t ^ j * (chainPolynomial β m j).eval t⁻¹) := by
      filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with t ht
      exact ih j ht
    have hd (j : ℕ) := (heq j).deriv_eq.trans (polynomial_product_hasDeriv β hz j
      (chainPolynomial β m j)).deriv
    cases k with
    | zero =>
      rw [ExactChange.chainCoeff, hd]
      simp [chainPolynomial]
    | succ k =>
      change deriv (ExactChange.chainCoeff (phaseDerivative β) m (k + 1)) z +
        phaseDerivative β z * ExactChange.chainCoeff (phaseDerivative β) m k z = _
      rw [hd, ih k hz]
      simp only [chainPolynomial, eval_add, eval_sub, eval_mul, eval_C, eval_one, eval_pow, eval_X]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring

/-- Local equality of phase derivatives gives local equality of the computed
chain coefficients, including the derivatives used by their recurrence. -/
lemma chainCoeff_congr_germ {q₁ q₂ : ℂ → ℂ} {z : ℂ}
    (hq : q₁ =ᶠ[𝓝 z] q₂) (m k : ℕ) :
    ExactChange.chainCoeff q₁ m k =ᶠ[𝓝 z] ExactChange.chainCoeff q₂ m k := by
  induction m generalizing k with
  | zero => cases k <;> exact Filter.EventuallyEq.rfl
  | succ m ih =>
    cases k with
    | zero => exact (ih 0).deriv
    | succ k =>
      filter_upwards [(ih (k + 1)).deriv, hq, ih k] with t hd hq hc
      simp only [ExactChange.chainCoeff, hd, hq, hc]

/-- Escape of the original coordinate makes each inverse-coordinate polynomial
converge to its constant term. -/
lemma polynomial_inverse_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun x => ‖t x‖) l atTop) (P : Polynomial ℂ) :
    Tendsto (fun x => P.eval (t x)⁻¹) l (𝓝 (P.eval 0)) := by
  have htc : Tendsto t l (Bornology.cobounded ℂ) := tendsto_norm_atTop_iff_cobounded.mp ht
  exact P.continuous.continuousAt.tendsto.comp (tendsto_inv₀_cobounded.comp htc)

/-- The all-order chain growth estimate is derived from the explicit polynomial
formula, rather than assumed. No growth assumption on the phase derivative is
needed for this estimate itself. -/
theorem chainCoeff_isBigO {α : Type*} {l : Filter α} {t : α → ℂ} (β : ℂ)
    (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hslit : ∀ᶠ x in l, t x ∈ Complex.slitPlane) (m k : ℕ) :
    (fun x => ExactChange.chainCoeff (phaseDerivative β) m k (t x)) =O[l]
      (fun x => phaseDerivative β (t x) ^ k) := by
  have hp := (polynomial_inverse_limit ht (chainPolynomial β m k)).isBigO_one ℂ
  have hb := (isBigO_refl (fun x => phaseDerivative β (t x) ^ k) l).mul hp
  have heq : (fun x => ExactChange.chainCoeff (phaseDerivative β) m k (t x)) =ᶠ[l]
      (fun x => phaseDerivative β (t x) ^ k * (chainPolynomial β m k).eval (t x)⁻¹) := by
    filter_upwards [hslit] with x hx
    exact chainCoeff_polynomial β m k hx
  simpa only [mul_one] using hb.congr' heq.symm Filter.EventuallyEq.rfl

/-- The same actual-chain estimate for any forward map whose derivative agrees
with the prescribed phase derivative on the logarithm branch domain. -/
theorem forward_chainCoeff_isBigO {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} (β : ℂ)
    (hΦ : ∀ z ∈ Complex.slitPlane, deriv Φ z = phaseDerivative β z)
    (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hslit : ∀ᶠ x in l, t x ∈ Complex.slitPlane) (m k : ℕ) :
    (fun x => ExactChange.chainCoeff (deriv Φ) m k (t x)) =O[l]
      (fun x => deriv Φ (t x) ^ k) := by
  have heq : (fun x => ExactChange.chainCoeff (deriv Φ) m k (t x)) =ᶠ[l]
      (fun x => ExactChange.chainCoeff (phaseDerivative β) m k (t x)) := by
    filter_upwards [hslit] with x hx
    have hg : deriv Φ =ᶠ[𝓝 (t x)] phaseDerivative β := by
      filter_upwards [Complex.isOpen_slitPlane.mem_nhds hx] with z hz
      exact hΦ z hz
    exact (chainCoeff_congr_germ hg m k).eq_of_nhds
  have hp : (fun x => deriv Φ (t x) ^ k) =ᶠ[l]
      (fun x => phaseDerivative β (t x) ^ k) := by
    filter_upwards [hslit] with x hx
    rw [hΦ (t x) hx]
  exact (chainCoeff_isBigO β ht hslit m k).congr' heq.symm hp.symm

lemma norm_phaseDerivative (β : ℝ) {z : ℂ} (hz : z ≠ 0) :
    ‖phaseDerivative (β : ℂ) z‖ = ‖z‖ ^ β * Real.exp z.re := by
  unfold phaseDerivative
  rw [Complex.norm_exp]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.log_re]
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), Real.exp_add]
  congr 1
  ring

lemma coordinate_norm_tendsto {α : Type*} {l : Filter α} {t : α → ℂ}
    (ht : Tendsto (fun x => (t x).re) l atTop) :
    Tendsto (fun x => ‖t x‖) l atTop :=
  tendsto_atTop_mono (fun x => Complex.re_le_norm (t x)) ht

/-- For the admissible real nonnegative exponent, phase-derivative norm escapes
to infinity whenever the original coordinate's real part does. A bounded strip
is sufficient but is not needed for this conclusion. -/
theorem norm_phaseDerivative_tendsto {α : Type*} {l : Filter α} {t : α → ℂ}
    {β : ℝ} (hβ : 0 ≤ β) (ht : Tendsto (fun x => (t x).re) l atTop) :
    Tendsto (fun x => ‖phaseDerivative (β : ℂ) (t x)‖) l atTop := by
  have hn := coordinate_norm_tendsto ht
  apply tendsto_atTop_mono' l ?_ (Real.tendsto_exp_atTop.comp ht)
  filter_upwards [hn.eventually_ge_atTop 1] with x hx
  have hpos : 0 < ‖t x‖ := by linarith
  change Real.exp (t x).re ≤ ‖phaseDerivative (β : ℂ) (t x)‖
  rw [norm_phaseDerivative β (norm_pos_iff.mp hpos)]
  have hp := Real.one_le_rpow hx hβ
  nlinarith [Real.exp_pos (t x).re]

/-- The phase coefficient limit with the actual chain growth estimate discharged
for the prescribed `t^β exp t` phase derivative. -/
theorem prescribed_phaseCoeff_limit {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} {B : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {n k : ℕ} (hk : k < n)
    {β : ℝ} (hβ : 0 ≤ β)
    (hΦ : ∀ z ∈ Complex.slitPlane, deriv Φ z = phaseDerivative (β : ℂ) z)
    (ht : Tendsto (fun x => (t x).re) l atTop)
    (hB : ∀ j < n, Tendsto (fun x => B j (t x) / deriv Φ (t x) ^ (n - j)) l (𝓝 (c j))) :
    Tendsto (fun x => ExactChange.phaseCoeff n B Φ k (t x)) l (𝓝 (c k)) := by
  have hs : ∀ᶠ x in l, t x ∈ Complex.slitPlane := by
    filter_upwards [ht.eventually_gt_atTop 0] with x hx
    exact Complex.mem_slitPlane_iff.mpr (Or.inl hx)
  have hq : Tendsto (fun x => ‖deriv Φ (t x)‖) l atTop := by
    refine (norm_phaseDerivative_tendsto hβ ht).congr' ?_
    filter_upwards [hs] with x hx
    rw [hΦ (t x) hx]
  apply PhaseCoefficientLimits.phaseCoeff_limit hk hq hB
  intro m hm j
  exact forward_chainCoeff_isBigO (β : ℂ) hΦ (coordinate_norm_tendsto ht) hs m j

lemma chainCoeff_first_column (q : ℂ → ℂ) (m : ℕ) :
    ExactChange.chainCoeff q (m + 1) 1 = iteratedDeriv m q := by
  induction m with
  | zero => funext z; simp [ExactChange.chainCoeff]
  | succ m ih =>
    funext z
    change deriv (ExactChange.chainCoeff q (m + 1) 1) z +
      q z * ExactChange.chainCoeff q (m + 1) 0 z = iteratedDeriv (m + 1) q z
    rw [ExactChange.chainCoeff_zero_column, ih, iteratedDeriv_succ]
    simp

/-- Every fixed derivative of the prescribed phase derivative is `O(q)`, with
an actual formula given by the first column of the chain polynomial family. -/
theorem iteratedDeriv_isBigO {α : Type*} {l : Filter α} {t : α → ℂ} (β : ℂ)
    (ht : Tendsto (fun x => ‖t x‖) l atTop)
    (hslit : ∀ᶠ x in l, t x ∈ Complex.slitPlane) (m : ℕ) :
    (fun x => iteratedDeriv m (phaseDerivative β) (t x)) =O[l]
      (fun x => phaseDerivative β (t x)) := by
  simpa only [chainCoeff_first_column, pow_one] using chainCoeff_isBigO β ht hslit (m + 1) 1

/-- Domain-local version: the forward-map derivative identity is needed only on
its actual open domain, not on the whole slit plane. -/
theorem forward_chainCoeff_isBigO_on {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (β : ℂ)
    (hΦ : ∀ z ∈ U, deriv Φ z = phaseDerivative β z)
    (ht : Tendsto (fun x => ‖t x‖) l atTop) (hdom : ∀ᶠ x in l, t x ∈ U)
    (hslit : ∀ᶠ x in l, t x ∈ Complex.slitPlane) (m k : ℕ) :
    (fun x => ExactChange.chainCoeff (deriv Φ) m k (t x)) =O[l]
      (fun x => deriv Φ (t x) ^ k) := by
  have heq : (fun x => ExactChange.chainCoeff (deriv Φ) m k (t x)) =ᶠ[l]
      (fun x => ExactChange.chainCoeff (phaseDerivative β) m k (t x)) := by
    filter_upwards [hdom] with x hx
    have hg : deriv Φ =ᶠ[𝓝 (t x)] phaseDerivative β := by
      filter_upwards [hU.mem_nhds hx] with z hz
      exact hΦ z hz
    exact (chainCoeff_congr_germ hg m k).eq_of_nhds
  have hp : (fun x => deriv Φ (t x) ^ k) =ᶠ[l]
      (fun x => phaseDerivative β (t x) ^ k) := by
    filter_upwards [hdom] with x hx
    rw [hΦ (t x) hx]
  exact (chainCoeff_isBigO β ht hslit m k).congr' heq.symm hp.symm

theorem prescribed_phaseCoeff_limit_on {α : Type*} {l : Filter α} {t : α → ℂ}
    {Φ : ℂ → ℂ} {B : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {n k : ℕ} (hk : k < n)
    {β : ℝ} (hβ : 0 ≤ β) {U : Set ℂ} (hU : IsOpen U)
    (hΦ : ∀ z ∈ U, deriv Φ z = phaseDerivative (β : ℂ) z)
    (ht : Tendsto (fun x => (t x).re) l atTop) (hdom : ∀ᶠ x in l, t x ∈ U)
    (hB : ∀ j < n, Tendsto (fun x => B j (t x) / deriv Φ (t x) ^ (n - j)) l (𝓝 (c j))) :
    Tendsto (fun x => ExactChange.phaseCoeff n B Φ k (t x)) l (𝓝 (c k)) := by
  have hs : ∀ᶠ x in l, t x ∈ Complex.slitPlane := by
    filter_upwards [ht.eventually_gt_atTop 0] with x hx
    exact Complex.mem_slitPlane_iff.mpr (Or.inl hx)
  have hq : Tendsto (fun x => ‖deriv Φ (t x)‖) l atTop := by
    refine (norm_phaseDerivative_tendsto hβ ht).congr' ?_
    filter_upwards [hdom] with x hx
    rw [hΦ (t x) hx]
  apply PhaseCoefficientLimits.phaseCoeff_limit hk hq hB
  intro m hm j
  exact forward_chainCoeff_isBigO_on hU (β : ℂ) hΦ (coordinate_norm_tendsto ht) hdom hs m j

end
end ZeroDensity.PhaseDerivativeBounds
