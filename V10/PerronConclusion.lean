import ZeroDensity.Perron
import ZeroDensity.PerronEstimates
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-!
# The finite-spectrum conclusion in Perron's theorem

This is the final real-analysis step, with the spectral-cut estimates explicit.
The ODE modules must prove those estimates from the differential equation.
No convergence of the logarithmic growth is assumed here.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace V10.PerronConclusion

/-- A bounded real function whose tail lies strictly on one side of every
non-spectral cut converges to an element of the finite spectrum. -/
theorem tendsto_mem_finite_of_cut_dichotomy {α : Type*} {l : Filter α} [NeBot l]
    {u : α → ℝ} {S : Set ℝ} (hS : S.Finite)
    (hupper : l.IsBoundedUnder (· ≤ ·) u)
    (hlower : l.IsBoundedUnder (· ≥ ·) u)
    (hcut : ∀ γ ∉ S, ∃ δ > 0,
      (∀ᶠ t in l, u t ≤ γ - δ) ∨ (∀ᶠ t in l, γ + δ ≤ u t)) :
    ∃ ℓ ∈ S, Tendsto u l (𝓝 ℓ) := by
  have hdense : Dense Sᶜ := by
    convert (dense_univ : Dense (Set.univ : Set ℝ)).sdiff_finite hS using 1
    ext x
    simp only [mem_compl_iff, Set.mem_sdiff, mem_univ, true_and]
  obtain ⟨ℓ, hℓ⟩ := tendsto_of_no_upcrossings hdense (u := u) (f := l)
    (fun a ha b _ hab ⟨hlo, hhi⟩ => by
      obtain ⟨δ, hδ, h | h⟩ := hcut a ha
      · obtain ⟨t, ht, ht'⟩ := (hhi.and_eventually h).exists
        linarith
      · obtain ⟨t, ht, ht'⟩ := (hlo.and_eventually h).exists
        linarith) hupper hlower
  refine ⟨ℓ, ?_, hℓ⟩
  by_contra hn
  obtain ⟨δ, hδ, h | h⟩ := hcut ℓ hn
  · have hh : ℓ ≤ ℓ - δ := le_of_tendsto hℓ h
    linarith
  · have hh : ℓ + δ ≤ ℓ := ge_of_tendsto hℓ h
    linarith

/-- The exact normalized logarithm of an exponential comparison function. -/
theorem log_exp_comparison_tendsto {C : ℝ} (hC : 0 < C) (k T : ℝ) :
    Tendsto (fun t : ℝ => Real.log (C * Real.exp (k * (t - T))) / t)
      atTop (𝓝 k) := by
  have h : Tendsto (fun t : ℝ => (Real.log C - k * T) / t + k)
      atTop (𝓝 k) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_id).add_const k
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _), Real.log_exp]
  field_simp
  ring

/-- Exponential upper estimates give eventual upper bounds for log growth,
with any prescribed positive loss. -/
theorem log_rate_eventually_le {f : ℝ → ℝ} {C k T ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hf : ∀ᶠ t in atTop, 0 < f t)
    (hbound : ∀ᶠ t in atTop, f t ≤ C * Real.exp (k * (t - T))) :
    ∀ᶠ t in atTop, Real.log (f t) / t ≤ k + ε := by
  have he := (log_exp_comparison_tendsto hC k T).eventually_lt_const
    (show k < k + ε by linarith)
  filter_upwards [hf, hbound, he, eventually_gt_atTop (0 : ℝ)] with t ht hb he ht0
  exact (div_le_div_of_nonneg_right (Real.log_le_log ht hb) ht0.le).trans he.le

/-- The lower exponential comparison gives the corresponding lower bound. -/
theorem eventually_le_log_rate {f : ℝ → ℝ} {C k T ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε)
    (hbound : ∀ᶠ t in atTop, C * Real.exp (k * (t - T)) ≤ f t) :
    ∀ᶠ t in atTop, k - ε ≤ Real.log (f t) / t := by
  have he := (log_exp_comparison_tendsto hC k T).eventually_const_lt
    (show k - ε < k by linarith)
  filter_upwards [hbound, he, eventually_gt_atTop (0 : ℝ)] with t hb he ht0
  exact he.le.trans (div_le_div_of_nonneg_right
    (Real.log_le_log (mul_pos hC (Real.exp_pos _)) hb) ht0.le)

section Norm
variable {E : Type*} [NormedAddCommGroup E]

/-- Passing an upper energy estimate through an actual lower norm comparison
loses only half of the strict spectral margin. -/
theorem log_norm_upper_of_energy {x : ℝ → E} {energy : ℝ → ℝ}
    {m C γ δ T : ℝ} (hm : 0 < m) (hC : 0 < C) (hδ : 0 < δ)
    (hx : ∀ᶠ t in atTop, x t ≠ 0)
    (hcompare : ∀ᶠ t in atTop, m * ‖x t‖ ^ 2 ≤ energy t)
    (hbound : ∀ᶠ t in atTop,
      energy t ≤ C * Real.exp (2 * (γ - δ) * (t - T))) :
    ∀ᶠ t in atTop, Real.log ‖x t‖ / t ≤ γ - δ / 2 := by
  have hb : ∀ᶠ t in atTop,
      ‖x t‖ ^ 2 ≤ (C / m) * Real.exp (2 * (γ - δ) * (t - T)) := by
    filter_upwards [hcompare, hbound] with t hc hb
    calc
      ‖x t‖ ^ 2 ≤ (C * Real.exp (2 * (γ - δ) * (t - T))) / m :=
        (le_div_iff₀ hm).mpr (by nlinarith [hc.trans hb])
      _ = _ := by ring
  have hh := log_rate_eventually_le (div_pos hC hm) hδ
    (hx.mono fun t ht => pow_pos (norm_pos_iff.mpr ht) 2) hb
  filter_upwards [hh] with t ht
  rw [Real.log_pow, mul_div_assoc] at ht
  norm_num at ht
  linarith

/-- Passing a lower energy estimate through an upper norm comparison. -/
theorem log_norm_lower_of_energy {x : ℝ → E} {energy : ℝ → ℝ}
    {M C γ δ T : ℝ} (hM : 0 < M) (hC : 0 < C) (hδ : 0 < δ)
    (hcompare : ∀ᶠ t in atTop, energy t ≤ M * ‖x t‖ ^ 2)
    (hbound : ∀ᶠ t in atTop,
      C * Real.exp (2 * (γ + δ) * (t - T)) ≤ energy t) :
    ∀ᶠ t in atTop, γ + δ / 2 ≤ Real.log ‖x t‖ / t := by
  have hb : ∀ᶠ t in atTop,
      (C / M) * Real.exp (2 * (γ + δ) * (t - T)) ≤ ‖x t‖ ^ 2 := by
    filter_upwards [hcompare, hbound] with t hc hb
    calc
      _ = (C * Real.exp (2 * (γ + δ) * (t - T))) / M := by ring
      _ ≤ ‖x t‖ ^ 2 := (div_le_iff₀ hM).mpr (by nlinarith [hb.trans hc])
  have hh := eventually_le_log_rate (div_pos hC hM) hδ hb
  filter_upwards [hh] with t ht
  rw [Real.log_pow, mul_div_assoc] at ht
  norm_num at ht
  linarith

end Norm

section ODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gronwall in both time directions gives bounded normalized logarithmic
growth for every nonzero solution of a bounded linear system on a tail. -/
theorem solution_log_rate_bounded {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {T K : ℝ}
    (hode : ∀ t ≥ T, HasDerivAt x (A t (x t)) t)
    (hA : ∀ t ≥ T, ‖A t‖ ≤ K) (hx : x T ≠ 0) :
    atTop.IsBoundedUnder (· ≤ ·) (fun t => Real.log ‖x t‖ / t) ∧
    atTop.IsBoundedUnder (· ≥ ·) (fun t => Real.log ‖x t‖ / t) := by
  have hne : ∀ᶠ t in atTop, x t ≠ 0 := by
    filter_upwards [eventually_ge_atTop T] with t ht
    exact ZeroDensity.PerronEstimates.solution_ne_zero ht
      (fun s hs => hode s hs.1) (fun s hs => hA s hs.1) hx
  have hu : ∀ᶠ t in atTop, ‖x t‖ ≤ ‖x T‖ * Real.exp (K * (t - T)) := by
    filter_upwards [eventually_ge_atTop T] with t ht
    exact ZeroDensity.PerronEstimates.solution_norm_upper ht
      (fun s hs => hode s hs.1) (fun s hs => hA s hs.1)
  have hl : ∀ᶠ t in atTop, ‖x T‖ * Real.exp ((-K) * (t - T)) ≤ ‖x t‖ := by
    filter_upwards [eventually_ge_atTop T] with t ht
    have hh := ZeroDensity.PerronEstimates.solution_norm_backward ht
      (fun s hs => hode s hs.1) (fun s hs => hA s hs.1)
    have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos ((-K) * (t - T))).le
    calc
      _ ≤ ‖x t‖ * Real.exp (K * (t - T)) * Real.exp ((-K) * (t - T)) := hh'
      _ = ‖x t‖ := by rw [mul_assoc, ← Real.exp_add]; simp
  exact ⟨isBoundedUnder_of_eventually_le
    (log_rate_eventually_le (norm_pos_iff.mpr hx) zero_lt_one
      (hne.mono fun _ ht => norm_pos_iff.mpr ht) hu),
    isBoundedUnder_of_eventually_ge
      (eventually_le_log_rate (norm_pos_iff.mpr hx) zero_lt_one hl)⟩

/-- Local boundedness of continuous coefficients propagates a nonzero initial
value along the entire half-line. No global coefficient bound is assumed. -/
theorem solution_ne_zero_halfline {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn A (Ici T))
    (hode : ∀ t ≥ T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0) :
    ∀ t ≥ T, x t ≠ 0 := by
  intro t ht
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.mono (show Icc T t ⊆ Ici T from fun _ hs => hs.1))
  exact ZeroDensity.PerronEstimates.solution_ne_zero ht
    (fun s hs => hode s hs.1) hK hx

/-- Convergence of the coefficient operator supplies the bounded-tail
hypothesis required for the logarithmic compactness step. -/
theorem solution_log_rate_bounded_of_tendsto {A : ℝ → E →L[ℝ] E}
    {A₀ : E →L[ℝ] E} {x : ℝ → E} {T : ℝ}
    (hcont : ContinuousOn A (Ici T)) (hlim : Tendsto A atTop (𝓝 A₀))
    (hode : ∀ t ≥ T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0) :
    atTop.IsBoundedUnder (· ≤ ·) (fun t => Real.log ‖x t‖ / t) ∧
    atTop.IsBoundedUnder (· ≥ ·) (fun t => Real.log ‖x t‖ / t) := by
  have hsmall : ∀ᶠ t in atTop, ‖A t‖ < ‖A₀‖ + 1 :=
    hlim.norm.eventually_lt_const (lt_add_one _)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hsmall
  exact solution_log_rate_bounded (T := max T T₁)
    (fun t ht => hode t ((le_max_left _ _).trans ht))
    (fun t ht => (hT₁ t ((le_max_right _ _).trans ht)).le)
    (solution_ne_zero_halfline hcont hode hx _ (le_max_left _ _))

end ODE

/-- Multiplicative comparison by fixed positive constants changes normalized
logarithms by a quantity tending to zero. -/
theorem log_rate_difference_tendsto_zero {f g : ℝ → ℝ} {C D : ℝ}
    (hC : 0 < C) (hD : 0 < D)
    (hf : ∀ᶠ t in atTop, 0 < f t) (hg : ∀ᶠ t in atTop, 0 < g t)
    (hfg : ∀ᶠ t in atTop, f t ≤ C * g t)
    (hgf : ∀ᶠ t in atTop, g t ≤ D * f t) :
    Tendsto (fun t => Real.log (f t) / t - Real.log (g t) / t) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => (-Real.log D) / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hu : Tendsto (fun t : ℝ => Real.log C / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hf, hg, hgf, eventually_gt_atTop (0 : ℝ)] with t hf hg hb ht
    have hh := Real.log_le_log hg hb
    rw [Real.log_mul (ne_of_gt hD) (ne_of_gt hf)] at hh
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) ht.le
  · filter_upwards [hf, hg, hfg, eventually_gt_atTop (0 : ℝ)] with t hf hg hb ht
    have hh := Real.log_le_log hf hb
    rw [Real.log_mul (ne_of_gt hC) (ne_of_gt hg)] at hh
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) ht.le

/-- A fixed continuous change of coordinates preserves logarithmic growth,
without requiring existence of either growth limit in advance. -/
theorem log_norm_equiv_difference_tendsto_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) {x : ℝ → E} (hx : ∀ᶠ t in atTop, x t ≠ 0) :
    Tendsto (fun t => Real.log ‖e (x t)‖ / t - Real.log ‖x t‖ / t)
      atTop (𝓝 0) := by
  apply log_rate_difference_tendsto_zero
    (C := max 1 ‖e.toContinuousLinearMap‖)
    (D := max 1 ‖e.symm.toContinuousLinearMap‖)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  · filter_upwards [hx] with t ht
    apply norm_pos_iff.mpr
    intro he
    apply ht
    exact e.injective (by simpa using he)
  · exact hx.mono fun _ ht => norm_pos_iff.mpr ht
  · exact Eventually.of_forall fun t => (e.toContinuousLinearMap.le_opNorm (x t)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · apply Eventually.of_forall
    intro t
    have hh := e.symm.toContinuousLinearMap.le_opNorm (e (x t))
    simpa using hh.trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 _) (norm_nonneg _))

/-- Strict alternatives survive a change of coordinates: half the margin
absorbs the vanishing normalized-log discrepancy. -/
theorem cut_dichotomy_of_difference_tendsto_zero {u v : ℝ → ℝ} {γ δ : ℝ}
    (hδ : 0 < δ) (hdiff : Tendsto (fun t => v t - u t) atTop (𝓝 0))
    (hcut : (∀ᶠ t in atTop, v t ≤ γ - δ) ∨ (∀ᶠ t in atTop, γ + δ ≤ v t)) :
    (∀ᶠ t in atTop, u t ≤ γ - δ / 2) ∨
      (∀ᶠ t in atTop, γ + δ / 2 ≤ u t) := by
  rcases hcut with h | h
  · left
    have he := hdiff.eventually_const_lt (show -δ / 2 < 0 by linarith)
    filter_upwards [h, he] with t ht he
    linarith
  · right
    have he := hdiff.eventually_lt_const (show 0 < δ / 2 by linarith)
    filter_upwards [h, he] with t ht he
    linarith

end V10.PerronConclusion
