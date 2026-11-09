import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Constructions

/-!
Concrete analytic estimates used by the scalar/jet comparison in the indicator-limit lemma.
This file does not assert subharmonic compactness or the scalar L¹ convergence theorem.
The jet uses the finite-product sup norm; equivalence of finite-dimensional norms makes
this sufficient for logarithmic asymptotics.
-/
namespace ZeroDensity.ScalarLimit
open Metric
noncomputable section

/-- The actual derivative jet of a scalar analytic function. -/
def jet (n : ℕ) (v : ℂ → ℂ) (z : ℂ) : Fin n → ℂ :=
  fun j => iteratedDeriv j.val v z

/-- The first coordinate of the actual jet is the scalar function itself. -/
lemma norm_scalar_le_jet {n : ℕ} (hn : 0 < n) (v : ℂ → ℂ) (z : ℂ) :
    ‖v z‖ ≤ ‖jet n v z‖ := by
  simpa [jet] using norm_le_pi_norm (jet n v z) (⟨0, hn⟩ : Fin n)

/-- Scalar log is below jet log away from scalar zeros. A subharmonic formalization
must handle zeros by extended-real `-∞`, rather than mathlib's `Real.log 0 = 0`. -/
lemma log_scalar_le_jet {n : ℕ} (hn : 0 < n) {v : ℂ → ℂ} {z : ℂ}
    (hv : v z ≠ 0) : Real.log ‖v z‖ ≤ Real.log ‖jet n v z‖ := by
  exact Real.log_le_log (norm_pos_iff.mpr hv) (norm_scalar_le_jet hn v z)

/-- A positive Cauchy constant depending only on the disk radius and jet length. -/
def cauchyConstant (n : ℕ) (δ : ℝ) : ℝ :=
  1 + ∑ j : Fin n, (j.val.factorial : ℝ) / δ ^ j.val

lemma cauchyConstant_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    0 < cauchyConstant n δ := by
  unfold cauchyConstant
  have : 0 ≤ ∑ j : Fin n, (j.val.factorial : ℝ) / δ ^ j.val :=
    Finset.sum_nonneg fun j _ => by positivity
  linarith

/-- Cauchy's estimate on a disk of radius `R δ` has an `R`-independent bound for `R ≥ 1`.
The function here is the original analytic function, not a supplied jet surrogate. -/
theorem derivative_bound_scaled_disk {v : ℂ → ℂ} {z : ℂ} {R δ M : ℝ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hv : DiffContOnCl ℂ v (ball z (R * δ)))
    (hbound : ∀ w ∈ sphere z (R * δ), ‖v w‖ ≤ M) (j : ℕ) :
    ‖iteratedDeriv j v z‖ ≤ (j.factorial : ℝ) / δ ^ j * M := by
  have hRp : 0 < R := by linarith
  have hrad : δ ≤ R * δ := by nlinarith
  have hp : δ ^ j ≤ (R * δ) ^ j := pow_le_pow_left₀ hδ.le hrad j
  calc
    ‖iteratedDeriv j v z‖ ≤ (j.factorial : ℝ) * M / (R * δ) ^ j :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j
        (mul_pos hRp hδ) hv hbound
    _ ≤ (j.factorial : ℝ) * M / δ ^ j :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hδ j) hp
    _ = (j.factorial : ℝ) / δ ^ j * M := by ring

/-- Finite-jet Cauchy comparison with a constant independent of the scaling parameter. -/
theorem jet_bound_scaled_disk {n : ℕ} {v : ℂ → ℂ} {z : ℂ} {R δ M : ℝ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hv : DiffContOnCl ℂ v (ball z (R * δ)))
    (hbound : ∀ w ∈ sphere z (R * δ), ‖v w‖ ≤ M) :
    ‖jet n v z‖ ≤ cauchyConstant n δ * M := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (cauchyConstant_pos hδ).le hM)).2
  intro j
  have hs : (j.val.factorial : ℝ) / δ ^ j.val ≤
      ∑ k : Fin n, (k.val.factorial : ℝ) / δ ^ k.val :=
    Finset.single_le_sum (f := fun k : Fin n => (k.val.factorial : ℝ) / δ ^ k.val) (fun k _ => by positivity) (Finset.mem_univ j)
  have hc : (j.val.factorial : ℝ) / δ ^ j.val ≤ cauchyConstant n δ := by
    unfold cauchyConstant
    linarith
  exact (derivative_bound_scaled_disk hR hδ hM hv hbound j.val).trans
    (mul_le_mul_of_nonneg_right hc hM)

/-- Logarithmic jet comparison, with the explicit vanishing error `(log C)/R`. -/
theorem log_jet_bound_scaled_disk {n : ℕ} {v : ℂ → ℂ} {z : ℂ} {R δ M : ℝ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hM : 0 < M) (hjet : 0 < ‖jet n v z‖)
    (hv : DiffContOnCl ℂ v (ball z (R * δ)))
    (hbound : ∀ w ∈ sphere z (R * δ), ‖v w‖ ≤ M) :
    Real.log ‖jet n v z‖ / R ≤
      Real.log M / R + Real.log (cauchyConstant n δ) / R := by
  have hb := jet_bound_scaled_disk (n := n) hR hδ hM.le hv hbound
  have hl := Real.log_le_log hjet hb
  rw [Real.log_mul (ne_of_gt (cauchyConstant_pos hδ)) (ne_of_gt hM)] at hl
  have hRp : 0 < R := by linarith
  calc
    Real.log ‖jet n v z‖ / R ≤
        (Real.log (cauchyConstant n δ) + Real.log M) / R :=
      div_le_div_of_nonneg_right hl hRp.le
    _ = Real.log M / R + Real.log (cauchyConstant n δ) / R := by ring

end
end ZeroDensity.ScalarLimit
