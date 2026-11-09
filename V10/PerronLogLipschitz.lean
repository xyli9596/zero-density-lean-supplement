import V10.PerronRadial
import Mathlib.Analysis.Convex.Basic

/-!
# Local equicontinuity of vector logarithmic potentials

Straight-line Gronwall proves the logarithmic Lipschitz bound directly from
the actual complex ODE. This works for any norm on the solution space and
does not assume differentiability of that norm.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace V10.PerronLogLipschitz
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A coefficient bound on a convex domain bounds changes in the logarithm
of the norm of a nonvanishing actual solution. -/
theorem log_norm_sub_le {D : Set ℂ} (hD : Convex ℝ D)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} {M : ℝ}
    (hode : ∀ z ∈ D, HasDerivAt Y (A z (Y z)) z)
    (hA : ∀ z ∈ D, ‖A z‖ ≤ M)
    {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) (hne : Y z ≠ 0) :
    |Real.log ‖Y w‖ - Real.log ‖Y z‖| ≤ M * ‖w - z‖ := by
  let path : ℝ → ℂ := fun t => z + (t : ℂ) * (w - z)
  let C : ℝ → E →L[ℝ] E := fun t =>
    (((w - z) • A (path t)) : E →L[ℂ] E).restrictScalars ℝ
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, path t ∈ D := by
    intro t ht
    simpa [path, Complex.real_smul] using hD.add_smul_sub_mem hz hw ht
  have hpder (t : ℝ) : HasDerivAt path (w - z) t := by
    simpa only [path, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - z)).const_add z
  have ho : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => Y (path t))
      (C t (Y (path t))) t := by
    intro t ht
    change HasDerivAt (fun t => Y (path t)) ((w - z) • (A (path t)) (Y (path t))) t
    exact (hode _ (hpath t ht)).scomp t (hpder t)
  have hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖C t‖ ≤ M * ‖w - z‖ := by
    intro t ht
    simp only [C, ContinuousLinearMap.norm_restrictScalars, norm_smul]
    calc
      ‖w - z‖ * ‖A (path t)‖ ≤ ‖w - z‖ * M :=
        mul_le_mul_of_nonneg_left (hA _ (hpath t ht)) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hh := ZeroDensity.PerronEstimates.solution_log_norm_bound
    (show (0 : ℝ) ≤ 1 by norm_num) ho hC (by simpa [path] using hne)
  simpa [path] using hh

/-- Rescaling the argument and dividing the logarithm by the same positive
scale cancels the growth of the differential coefficient. This is the
uniform local Lipschitz estimate for the vector potentials in Lemma 3.2. -/
theorem scaled_log_norm_sub_le {D : Set ℂ} (hD : Convex ℝ D)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} {M R : ℝ} (hR : 0 < R)
    (hode : ∀ ζ ∈ D, HasDerivAt Y
      (A ((R : ℂ) * ζ) (Y ((R : ℂ) * ζ))) ((R : ℂ) * ζ))
    (hA : ∀ ζ ∈ D, ‖A ((R : ℂ) * ζ)‖ ≤ M)
    {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) (hne : Y ((R : ℂ) * z) ≠ 0) :
    |Real.log ‖Y ((R : ℂ) * w)‖ / R - Real.log ‖Y ((R : ℂ) * z)‖ / R| ≤
      M * ‖w - z‖ := by
  have ho : ∀ ζ ∈ D, HasDerivAt (fun ζ => Y ((R : ℂ) * ζ))
      (((R : ℂ) • A ((R : ℂ) * ζ)) (Y ((R : ℂ) * ζ))) ζ := by
    intro ζ hζ
    simpa only [Function.comp_def, smul_apply, mul_one] using
      (hode ζ hζ).scomp ζ ((hasDerivAt_id ζ).const_mul (R : ℂ))
  have hbound : ∀ ζ ∈ D, ‖(R : ℂ) • A ((R : ℂ) * ζ)‖ ≤ R * M := by
    intro ζ hζ
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using
      mul_le_mul_of_nonneg_left (hA ζ hζ) hR.le
  have hh := log_norm_sub_le hD ho hbound hz hw hne
  rw [← sub_div, abs_div, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  nlinarith [hh]

/-- Any pointwise limit of the actual scaled vector potentials inherits the
same Lipschitz bound wherever the ODE coefficient bound holds eventually. -/
theorem limit_log_potential_sub_le {D : Set ℂ} (hD : Convex ℝ D)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} {H : ℂ → ℝ} {M : ℝ}
    (hode : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, HasDerivAt Y
      (A ((R : ℂ) * ζ) (Y ((R : ℂ) * ζ))) ((R : ℂ) * ζ))
    (hA : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, ‖A ((R : ℂ) * ζ)‖ ≤ M)
    (hne : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, Y ((R : ℂ) * ζ) ≠ 0)
    (hlim : ∀ ζ ∈ D, Tendsto (fun R : ℝ => Real.log ‖Y ((R : ℂ) * ζ)‖ / R)
      atTop (𝓝 (H ζ))) {z w : ℂ} (hz : z ∈ D) (hw : w ∈ D) :
    |H w - H z| ≤ M * ‖w - z‖ := by
  apply le_of_tendsto ((hlim w hw).sub (hlim z hz)).abs
  filter_upwards [hode, hA, hne, eventually_gt_atTop (0 : ℝ)] with R ho hA hn hR
  exact scaled_log_norm_sub_le hD hR ho hA hz hw (hn z hz)

#print axioms log_norm_sub_le
#print axioms scaled_log_norm_sub_le
#print axioms limit_log_potential_sub_le
end V10.PerronLogLipschitz
