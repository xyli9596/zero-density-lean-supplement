import V10.PerronDichotomyBasis
import V10.PerronSpectralAdapted
import V10.PerronConclusion

/-!
# General Perron growth classification for asymptotically constant complex ODEs

For an actual finite-dimensional system x' = A(t)x, continuous on a half-line
with A(t) → A₀ and nonzero initial value, logarithmic norm growth converges to
the real part of an actual eigenvalue of A₀. Spectral decomposition, adapted
coordinates, energy derivatives, cone dichotomy, and the finite-spectrum
conclusion are proved by the imported modules; none is an assumption here.
Repeated eigenvalues and arbitrary Jordan blocks are included.
-/

namespace V10.PerronGeneral
open Set Filter Module
open scoped Topology Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- The actual complex-linear system, viewed as a real-time differential
equation, has a nonvanishing trajectory and bounded logarithmic rate. -/
theorem complex_solution_bounds {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    {x : ℝ → E} {T : ℝ} (hcont : ContinuousOn A (Ici T))
    (hlim : Tendsto A atTop (𝓝 A₀))
    (hode : ∀ t ≥ T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0) :
    (∀ t ≥ T, x t ≠ 0) ∧
      atTop.IsBoundedUnder (· ≤ ·) (fun t => Real.log ‖x t‖ / t) ∧
      atTop.IsBoundedUnder (· ≥ ·) (fun t => Real.log ‖x t‖ / t) := by
  let r := ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ
  have hc : ContinuousOn (fun t => (A t).restrictScalars ℝ) (Ici T) :=
    r.continuous.comp_continuousOn hcont
  have hl : Tendsto (fun t => (A t).restrictScalars ℝ) atTop
      (𝓝 (A₀.restrictScalars ℝ)) := r.continuous.continuousAt.tendsto.comp hlim
  have ho : ∀ t ≥ T, HasDerivAt x ((A t).restrictScalars ℝ (x t)) t := hode
  exact ⟨PerronConclusion.solution_ne_zero_halfline hc ho hx,
    PerronConclusion.solution_log_rate_bounded_of_tendsto hc hl ho hx⟩

/-- Every nonspectral real cut gives a strict eventual upper or lower side
for the actual normalized logarithmic norm. The spectral energy estimates
and the exponential dichotomy are constructed inside this proof. -/
theorem actual_spectral_cut {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    {x : ℝ → E} {T₀ γ : ℝ} (hcont : ContinuousOn A (Ici T₀))
    (hlim : Tendsto A atTop (𝓝 A₀))
    (hode : ∀ t ≥ T₀, HasDerivAt x (A t (x t)) t) (hx : x T₀ ≠ 0)
    (hγ : ∀ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E), μ.val.re ≠ γ) :
    ∃ η > 0,
      (∀ᶠ t in atTop, Real.log ‖x t‖ / t ≤ γ - η) ∨
      (∀ᶠ t in atTop, γ + η ≤ Real.log ‖x t‖ / t) := by
  classical
  obtain ⟨δ, hδ, ι, fι, dι, b, s, hs, hu⟩ :=
    PerronSpectral.exists_adapted_energy A₀.toLinearMap γ hγ
  let _ := fι
  let _ := dι
  let e := PerronDichotomyBasis.basisCoordinates b
  let B : ℝ → E →L[ℂ] E := fun t => A t - A₀
  have hBcont : ContinuousOn B (Ici T₀) := hcont.sub continuous_const.continuousOn
  have hBlim : Tendsto B atTop (𝓝 0) := by simpa [B] using hlim.sub_const A₀
  have ho : ∀ t ≥ T₀, HasDerivAt x (A₀ (x t) + B t (x t)) t := by
    intro t ht
    simpa only [B, sub_apply, add_sub_cancel] using hode t ht
  have hs' : ∀ y, PerronDichotomyCoordinates.pairing s y
      (LinearMap.toMatrix b b A₀.toLinearMap *ᵥ y) ≤
        (γ - 2 * δ) * PerronDichotomyCoordinates.energy s y := by
    intro y
    rw [PerronDichotomyCoordinates.pairing_eq_re_sum]
    exact hs y
  have hu' : ∀ y, (γ + 2 * δ) * PerronDichotomyCoordinates.energy sᶜ y ≤
      PerronDichotomyCoordinates.pairing sᶜ y
        (LinearMap.toMatrix b b A₀.toLinearMap *ᵥ y) := by
    intro y
    rw [PerronDichotomyCoordinates.pairing_eq_re_sum]
    exact hu y
  obtain ⟨T, hT, hupper | hlower⟩ := PerronDichotomyBasis.basis_ode_dichotomy
    b s hδ ho hx hBcont hs' hu' hBlim
  · obtain ⟨C, hC, hc⟩ := hupper
    have hne : ∀ᶠ t in atTop, x t ≠ 0 := by
      filter_upwards [eventually_ge_atTop T₀] with t ht
      exact (complex_solution_bounds hcont hlim hode hx).1 t ht
    have hne' : ∀ᶠ t in atTop, e (x t) ≠ 0 := hne.mono fun t ht hz =>
      ht (e.injective (by simpa using hz))
    have hcmp : ∀ᶠ t in atTop,
        1 * ‖e (x t)‖ ^ 2 ≤ PerronDichotomyCoordinates.energy Finset.univ (e (x t)) :=
      Eventually.of_forall fun t => by simpa using PerronDichotomyCoordinates.norm_sq_le_energy (e (x t))
    have hb : ∀ᶠ t in atTop,
        PerronDichotomyCoordinates.energy Finset.univ (e (x t)) ≤
          C * Real.exp (2 * (γ - δ) * (t - T)) := by
      filter_upwards [eventually_ge_atTop T] with t ht
      exact hc t ht
    have hlog := PerronConclusion.log_norm_upper_of_energy zero_lt_one hC hδ hne' hcmp hb
    refine ⟨(δ / 2) / 2, by positivity, ?_⟩
    exact PerronConclusion.cut_dichotomy_of_difference_tendsto_zero (by positivity)
      (PerronConclusion.log_norm_equiv_difference_tendsto_zero e hne) (Or.inl hlog)
  · obtain ⟨T₁, hT₁, C, hC, hc⟩ := hlower
    have hne : ∀ᶠ t in atTop, x t ≠ 0 := by
      filter_upwards [eventually_ge_atTop T₀] with t ht
      exact (complex_solution_bounds hcont hlim hode hx).1 t ht
    have hM : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
    have hcmp : ∀ᶠ t in atTop,
        PerronDichotomyCoordinates.energy Finset.univ (e (x t)) ≤
          ((Fintype.card ι : ℝ) + 1) * ‖e (x t)‖ ^ 2 := by
      apply Eventually.of_forall
      intro t
      have hh := PerronDichotomyCoordinates.energy_le_card_norm_sq Finset.univ (e (x t))
      simp only [Finset.card_univ] at hh
      nlinarith [sq_nonneg ‖e (x t)‖]
    have hb : ∀ᶠ t in atTop,
        C * Real.exp (2 * (γ + δ) * (t - T₁)) ≤
          PerronDichotomyCoordinates.energy Finset.univ (e (x t)) := by
      filter_upwards [eventually_ge_atTop T₁] with t ht
      exact hc t ht
    have hlog := PerronConclusion.log_norm_lower_of_energy hM hC hδ hcmp hb
    refine ⟨(δ / 2) / 2, by positivity, ?_⟩
    exact PerronConclusion.cut_dichotomy_of_difference_tendsto_zero (by positivity)
      (PerronConclusion.log_norm_equiv_difference_tendsto_zero e hne) (Or.inr hlog)

/-- General Perron theorem for an actual finite-dimensional asymptotically
constant complex ODE, allowing arbitrary repeated roots and Jordan blocks.
The resulting exponent is the real part of an actual eigenvalue of A₀. -/
theorem perron_growth_exponent {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    {x : ℝ → E} {T : ℝ} (hcont : ContinuousOn A (Ici T))
    (hlim : Tendsto A atTop (𝓝 A₀))
    (hode : ∀ t ≥ T, HasDerivAt x (A t (x t)) t) (hx : x T ≠ 0) :
    ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      Tendsto (fun t => Real.log ‖x t‖ / t) atTop (𝓝 μ.val.re) := by
  classical
  let S : Set ℝ := Set.range (fun μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E) => μ.val.re)
  have hS : S.Finite := Set.finite_range _
  have hb := (complex_solution_bounds hcont hlim hode hx).2
  obtain ⟨ℓ, hℓ, hlimrate⟩ := PerronConclusion.tendsto_mem_finite_of_cut_dichotomy hS hb.1 hb.2
    (fun γ hγ => actual_spectral_cut hcont hlim hode hx (fun μ he =>
      hγ ⟨μ, he⟩))
  obtain ⟨μ, hμ⟩ := hℓ
  refine ⟨μ, ?_⟩
  change μ.val.re = ℓ at hμ
  rw [hμ]
  exact hlimrate

#print axioms complex_solution_bounds
#print axioms actual_spectral_cut
#print axioms perron_growth_exponent
end
end V10.PerronGeneral
