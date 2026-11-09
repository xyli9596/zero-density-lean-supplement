import V10.PerturbationGrowth
import ZeroDensity.PhaseDerivativeBounds
import Mathlib.Tactic

/-! Actual normalized perturbations decay exponentially on a sufficiently
narrow physical sector. This is the first coefficient estimate in the
proof of Theorem 1.5; moving inverse branches remain a separate obligation. -/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace V10.PerturbationSectorDecay
open ZeroDensity.PhaseDerivativeBounds

theorem exists_sector_gap {a b : ℝ} (ha : 0 < a) (hb : b < a) :
    ∃ κ : ℝ, 0 < κ ∧ 0 < 1 - (b / a) * Real.sqrt (1 + κ ^ 2) := by
  have hcont : ContinuousAt (fun κ : ℝ => (b / a) * Real.sqrt (1 + κ ^ 2)) 0 := by
    fun_prop
  have h0 : (b / a) * Real.sqrt (1 + (0 : ℝ) ^ 2) < 1 := by
    simpa using (div_lt_one ha).mpr hb
  have hev : ∀ᶠ κ : ℝ in 𝓝 0, (b / a) * Real.sqrt (1 + κ ^ 2) < 1 :=
    hcont.eventually (gt_mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε / 2, by linarith, ?_⟩
  have hk := hball (show ε / 2 ∈ ball (0 : ℝ) ε by
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < ε / 2)]
    linarith)
  exact sub_pos.mpr hk

theorem norm_le_sector {κ : ℝ} (_hκ : 0 ≤ κ) {t : ℂ} (ht : 0 ≤ t.re)
    (hi : |t.im| ≤ κ * t.re) : ‖t‖ ≤ Real.sqrt (1 + κ ^ 2) * t.re := by
  have hsq : t.im ^ 2 ≤ (κ * t.re) ^ 2 := by
    nlinarith [sq_abs t.im, abs_nonneg t.im, mul_nonneg _hκ ht]
  have hsqrt : Real.sqrt (1 + κ ^ 2) ^ 2 = 1 + κ ^ 2 :=
    Real.sq_sqrt (by positivity)
  apply (sq_le_sq₀ (norm_nonneg t) (mul_nonneg (Real.sqrt_nonneg _) ht)).mp
  rw [mul_pow, hsqrt, Complex.sq_norm, Complex.normSq_apply]
  nlinarith

/-- The normalized coefficient is the actual R(t/ω)/ω^m divided by the
actual phase derivative exp(β log t+t)^m. The constant and decay rate are
uniform throughout the thin sector; no inverse branch or limit is assumed. -/
theorem normalized_decay {R : ℂ → ℂ} {C b : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hR : ∀ z, ‖R z‖ ≤ C * Real.exp ((m : ℝ) * b * ‖z‖))
    {w : ℂ} (hw : w ≠ 0) {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    {t : ℂ} (ht : 1 ≤ t.re) (hi : |t.im| ≤ κ * t.re) :
    ‖(R (t / w) / w ^ m) / phaseDerivative (β : ℂ) t ^ m‖ ≤
      (C / ‖w‖ ^ m) *
        Real.exp (-((m : ℝ) * (1 - (b / ‖w‖) * Real.sqrt (1 + κ ^ 2))) * t.re) := by
  have ht0 : 0 < t.re := by linarith
  have htn : t ≠ 0 := by intro he; simp [he] at ht0
  have htnorm : 1 ≤ ‖t‖ := ht.trans (Complex.re_le_norm t)
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hpow : 1 ≤ ‖t‖ ^ β := Real.one_le_rpow htnorm hβ
  have hphase : Real.exp t.re ≤ ‖phaseDerivative (β : ℂ) t‖ := by
    rw [norm_phaseDerivative β htn]
    nlinarith [Real.exp_pos t.re]
  have hden : Real.exp ((m : ℝ) * t.re) ≤ ‖phaseDerivative (β : ℂ) t‖ ^ m := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hphase _
  have hexp : (m : ℝ) * b * (‖t‖ / ‖w‖) - (m : ℝ) * t.re ≤
      -((m : ℝ) * (1 - (b / ‖w‖) * Real.sqrt (1 + κ ^ 2))) * t.re := by
    have hn := norm_le_sector hκ ht0.le hi
    have hmul := mul_le_mul_of_nonneg_left hn
      (mul_nonneg (Nat.cast_nonneg m) (div_nonneg hb hwpos.le))
    simp only [div_eq_mul_inv] at hmul ⊢
    nlinarith only [hmul]
  rw [norm_div, norm_div, norm_pow, norm_pow]
  calc
    _ ≤ (C * Real.exp ((m : ℝ) * b * ‖t / w‖) / ‖w‖ ^ m) /
        Real.exp ((m : ℝ) * t.re) :=
      div_le_div₀ (div_nonneg (mul_nonneg hC (Real.exp_nonneg _)) (pow_nonneg (norm_nonneg _) _))
        (div_le_div_of_nonneg_right (hR (t / w)) (pow_nonneg (norm_nonneg _) _))
        (Real.exp_pos _) hden
    _ = (C / ‖w‖ ^ m) *
        Real.exp ((m : ℝ) * b * (‖t‖ / ‖w‖) - (m : ℝ) * t.re) := by
      rw [norm_div, Real.exp_sub]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp)
      (div_nonneg hC (pow_nonneg hwpos.le _))

/-- The original strict entire-type hypotheses give one sector and one
positive exponential gap for the whole finite family and every direction
of modulus a. In particular the new normalized coefficients vanish there. -/
theorem finite_family_sector_decay {ι : Type*} [Fintype ι] [Nonempty ι]
    {R : ι → ℂ → ℂ} {m : ι → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : ∀ i, 0 < m i) (hR : ∀ i, AnalyticOnNhd ℂ (R i) univ)
    (ht : ∀ i, ExponentialType.typeOneSphere (R i) <
      (((m i : ℝ) * a : ℝ) : EReal)) :
    ∃ b C κ : ℝ, 0 < b ∧ b < a ∧ 0 < C ∧ 0 < κ ∧
      0 < 1 - (b / a) * Real.sqrt (1 + κ ^ 2) ∧
      ∀ w : ℂ, ‖w‖ = a → ∀ β : ℝ, 0 ≤ β → ∀ i : ι,
        ∀ t : ℂ, 1 ≤ t.re → |t.im| ≤ κ * t.re →
          ‖(R i (t / w) / w ^ m i) / phaseDerivative (β : ℂ) t ^ m i‖ ≤
            (C / a ^ m i) * Real.exp (-((m i : ℝ) *
              (1 - (b / a) * Real.sqrt (1 + κ ^ 2))) * t.re) := by
  obtain ⟨b, C, hb, hba, hC, hg⟩ := PerturbationGrowth.finite_family_growth ha hR
    (fun i => by exact_mod_cast hm i) ht
  obtain ⟨κ, hκ, hgap⟩ := exists_sector_gap ha hba
  refine ⟨b, C, κ, hb, hba, hC, hκ, hgap, ?_⟩
  intro w hw β hβ i t htre htim
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hw ▸ ha)
  simpa only [hw] using normalized_decay hC.le hb.le (hg i) hw0 hβ hκ.le htre htim

/-- The pointwise sector bound implies actual normalized coefficient
convergence along every eventually contained path whose real part escapes. -/
theorem normalized_tendsto_zero {X : Type*} {l : Filter X}
    {R : ℂ → ℂ} {C b : ℝ} {m : ℕ} (hm : 0 < m)
    (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hR : ∀ z, ‖R z‖ ≤ C * Real.exp ((m : ℝ) * b * ‖z‖))
    {w : ℂ} (hw : w ≠ 0) {β κ : ℝ} (hβ : 0 ≤ β) (hκ : 0 ≤ κ)
    (hgap : 0 < 1 - (b / ‖w‖) * Real.sqrt (1 + κ ^ 2))
    {t : X → ℂ} (hre : Tendsto (fun x => (t x).re) l atTop)
    (hi : ∀ᶠ x in l, |(t x).im| ≤ κ * (t x).re) :
    Tendsto (fun x => (R (t x / w) / w ^ m) /
      phaseDerivative (β : ℂ) (t x) ^ m) l (𝓝 0) := by
  have hmg : 0 < (m : ℝ) * (1 - (b / ‖w‖) * Real.sqrt (1 + κ ^ 2)) :=
    mul_pos (by exact_mod_cast hm) hgap
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hre.const_mul_atTop hmg)
  have hzero : Tendsto (fun x => (C / ‖w‖ ^ m) * Real.exp
      (-((m : ℝ) * (1 - (b / ‖w‖) * Real.sqrt (1 + κ ^ 2))) * (t x).re))
      l (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using hexp.const_mul (C / ‖w‖ ^ m)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hzero
  filter_upwards [hre.eventually_ge_atTop 1, hi] with x hx hix
  exact normalized_decay hC hb hR hw hβ hκ hx hix

#print axioms exists_sector_gap
#print axioms normalized_decay
#print axioms finite_family_sector_decay
#print axioms normalized_tendsto_zero
end V10.PerturbationSectorDecay
