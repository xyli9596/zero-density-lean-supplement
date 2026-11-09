import V10.PerronGeneral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Logarithmic rates and bounded exponentially shifted trajectories

These real-analysis implications connect the actual bounded-solution space
constructed by Volterra theory to the slow spectral rates in Lemma 3.6.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace V10.PerronSlowRates
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def weighted (γ : ℝ) (x : ℝ → E) (t : ℝ) : E :=
  Complex.exp ((-γ * t : ℝ) : ℂ) • x t

theorem norm_weighted (γ : ℝ) (x : ℝ → E) (t : ℝ) :
    ‖weighted γ x t‖ = Real.exp (-γ * t) * ‖x t‖ := by
  simp [weighted, norm_smul, Complex.norm_exp]

theorem weighted_continuousOn {x : ℝ → E} {S : Set ℝ} (γ : ℝ)
    (hcont : ContinuousOn x S) : ContinuousOn (weighted γ x) S := by
  apply ContinuousOn.smul _ hcont
  fun_prop

/-- The exponential shift satisfies its actual shifted complex-linear ODE. -/
theorem weighted_hasDerivAt {A : ℝ → E →L[ℂ] E} {x : ℝ → E} {γ t : ℝ}
    (hx : HasDerivAt x (A t (x t)) t) :
    HasDerivAt (weighted γ x)
      ((A t - (γ : ℂ) • ContinuousLinearMap.id ℂ E) (weighted γ x t)) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp ((-γ * s : ℝ) : ℂ))
      ((-γ : ℂ) * Complex.exp ((-γ * t : ℝ) : ℂ)) t := by
    simpa only [id_eq, mul_one, Complex.ofReal_neg, mul_comm] using
      (((hasDerivAt_id t).const_mul (-γ)).ofReal_comp).cexp
  have hh := he.smul hx
  convert hh using 1
  · rfl
  · simp only [weighted, sub_apply, smul_apply, ContinuousLinearMap.id_apply, map_smul]
    module

/-- A strict gap between the actual logarithmic rate and the exponential
weight makes the shifted trajectory tend to zero. -/
theorem weighted_tendsto_zero {x : ℝ → E} {ℓ γ : ℝ}
    (hlim : Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 ℓ))
    (hne : ∀ᶠ t in atTop, x t ≠ 0) (hgap : ℓ < γ) :
    Tendsto (weighted γ x) atTop (𝓝 0) := by
  let k := (ℓ + γ) / 2
  have hlk : ℓ < k := by dsimp [k]; linarith
  have hkg : 0 < γ - k := by dsimp [k]; linarith
  have hupper := hlim.eventually_lt_const hlk
  have he : Tendsto (fun t : ℝ => Real.exp (-(t * (γ - k)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hkg)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ he
  filter_upwards [hupper, hne, eventually_gt_atTop (0 : ℝ)] with t ht hn ht0
  have hlog : Real.log ‖x t‖ ≤ k * t := (div_le_iff₀ ht0).mp ht.le
  have hx : ‖x t‖ ≤ Real.exp (k * t) := by
    rw [← Real.exp_log (norm_pos_iff.mpr hn)]
    exact Real.exp_le_exp.mpr hlog
  rw [norm_weighted]
  calc
    _ ≤ Real.exp (-γ * t) * Real.exp (k * t) :=
      mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Continuity upgrades decay on the tail to boundedness on the entire
closed half-line, including the initial compact segment. -/
theorem weighted_bounded_of_rate_lt {x : ℝ → E} {T ℓ γ : ℝ}
    (hcont : ContinuousOn x (Ici T))
    (hlim : Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 ℓ))
    (hne : ∀ᶠ t in atTop, x t ≠ 0) (hgap : ℓ < γ) :
    ∃ C : ℝ, ∀ t ≥ T, ‖weighted γ x t‖ ≤ C := by
  have hw : ContinuousOn (weighted γ x) (Ici T) := by
    apply ContinuousOn.smul _ hcont
    fun_prop
  have hl := (weighted_tendsto_zero hlim hne hgap).norm
  have he : ∀ᶠ t in atTop, ‖weighted γ x t‖ < 1 :=
    hl.eventually_lt_const (by simp)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 he
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hw.mono (show Icc T T₁ ⊆ Ici T from fun _ ht => ht.1))
  refine ⟨max C 1, fun t ht => ?_⟩
  rcases le_total t T₁ with h | h
  · exact (hC t ⟨ht, h⟩).trans (le_max_left _ _)
  · exact (hT₁ t h).le.trans (le_max_right _ _)

/-- Boundedness of the actual exponentially shifted trajectory constrains
its logarithmic rate. No ODE or spectral assumptions are needed for this step. -/
theorem rate_le_of_weighted_bounded {x : ℝ → E} {ℓ γ : ℝ}
    (hlim : Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 ℓ))
    (hne : ∀ᶠ t in atTop, x t ≠ 0)
    (hbounded : ∃ C : ℝ, ∀ᶠ t in atTop, ‖weighted γ x t‖ ≤ C) : ℓ ≤ γ := by
  obtain ⟨C, hC⟩ := hbounded
  let D := max 1 C
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hexp := PerronConclusion.log_exp_comparison_tendsto hD γ 0
  apply le_of_tendsto_of_tendsto hlim hexp
  filter_upwards [hC, hne, eventually_gt_atTop (0 : ℝ)] with t ht hn ht0
  have hb : ‖x t‖ ≤ D * Real.exp (γ * (t - 0)) := by
    have hh := mul_le_mul_of_nonneg_left (ht.trans (le_max_right 1 C))
      (Real.exp_pos (γ * t)).le
    rw [norm_weighted, ← mul_assoc, ← Real.exp_add] at hh
    simpa [D, mul_comm] using hh
  exact div_le_div_of_nonneg_right (Real.log_le_log (norm_pos_iff.mpr hn) hb) ht0.le

/-- Away from a spectral cut, bounded shifted solutions are exactly those
whose actual rate is strictly below the cut. -/
theorem weighted_bounded_iff_rate_lt {x : ℝ → E} {T ℓ γ : ℝ}
    (hcont : ContinuousOn x (Ici T))
    (hlim : Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 ℓ))
    (hne : ∀ᶠ t in atTop, x t ≠ 0) (hnecut : ℓ ≠ γ) :
    (∃ C : ℝ, ∀ t ≥ T, ‖weighted γ x t‖ ≤ C) ↔ ℓ < γ := by
  constructor
  · rintro ⟨C, hC⟩
    have hb : ∃ C : ℝ, ∀ᶠ t in atTop, ‖weighted γ x t‖ ≤ C := by
      refine ⟨C, ?_⟩
      filter_upwards [eventually_ge_atTop T] with t ht using hC t ht
    exact lt_of_le_of_ne (rate_le_of_weighted_bounded hlim hne hb) hnecut
  · exact weighted_bounded_of_rate_lt hcont hlim hne

/-- Boundedness of the weighted trajectory is invariant under the actual
fixed continuous change of coordinates used in the Jordan construction. -/
theorem weighted_bounded_equiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) {x : ℝ → E} {T γ : ℝ} :
    (∃ C : ℝ, ∀ t ≥ T, ‖weighted γ (fun t => e (x t)) t‖ ≤ C) ↔
      ∃ C : ℝ, ∀ t ≥ T, ‖weighted γ x t‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨‖e.symm.toContinuousLinearMap‖ * C, fun t ht => ?_⟩
    have hh := e.symm.toContinuousLinearMap.le_opNorm (weighted γ (fun t => e (x t)) t)
    calc
      _ = ‖e.symm (weighted γ (fun t => e (x t)) t)‖ := by simp [weighted]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖weighted γ (fun t => e (x t)) t‖ := hh
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)
  · rintro ⟨C, hC⟩
    refine ⟨‖e.toContinuousLinearMap‖ * C, fun t ht => ?_⟩
    calc
      _ = ‖e (weighted γ x t)‖ := by simp [weighted]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖weighted γ x t‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg _)

/-- The general ODE supplies the actual rate, and the nonspectral-cut
criterion then identifies bounded shifted solutions with slow rates. -/
theorem perron_weighted_bounded_iff [FiniteDimensional ℂ E]
    {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {x : ℝ → E} {T γ : ℝ}
    (hcont : ContinuousOn A (Ici T)) (hlim : Tendsto A atTop (𝓝 A₀))
    (hode : ∀ t ≥ T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0)
    (hγ : ∀ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      μ.val.re ≠ γ) :
    ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 μ.val.re) ∧
      ((∃ C : ℝ, ∀ t ≥ T, ‖weighted γ x t‖ ≤ C) ↔ μ.val.re < γ) := by
  obtain ⟨μ, hμ⟩ := PerronGeneral.perron_growth_exponent hcont hlim hode hx
  have hxc : ContinuousOn x (Ici T) := fun t ht =>
    (hode t ht).continuousAt.continuousWithinAt
  have hxn : ∀ᶠ t in atTop, x t ≠ 0 := by
    filter_upwards [eventually_ge_atTop T] with t ht
    exact (PerronGeneral.complex_solution_bounds hcont hlim hode hx).1 t ht
  exact ⟨μ, hμ, weighted_bounded_iff_rate_lt hxc hμ hxn (hγ μ)⟩

#print axioms weighted_tendsto_zero
#print axioms weighted_bounded_iff_rate_lt
#print axioms weighted_bounded_equiv
#print axioms perron_weighted_bounded_iff
end V10.PerronSlowRates
