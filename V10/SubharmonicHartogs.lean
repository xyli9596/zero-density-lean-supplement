import Ray.Hartogs.Subharmonic
import Ray.Hartogs.MaxLog
import Mathlib.Tactic

/-!
# Hartogs bounds for actual analytic norms

This adapter uses Geoffrey Irving's Ray library, copied without modification
at commit 74f0059c4fd01d606969a0de2d567249ed82d55e (Apache-2.0), with the same
Lean and mathlib pins as this project. See `Ray/LICENSE` and the audit record.

The truncated logarithm is `log (max (exp (L*q)) ‖f z‖) / q`; in particular it
has value L at a zero, even when L < 0. It is not the totalized expression
`max L (Real.log ‖f z‖ / q)` at zeros. Analyticity proves its subharmonicity.
Pointwise eventual exponential bounds, together with a common exponential
bound on the domain, then imply eventual uniform bounds on interior compact
sets. This is a genuine compact upper-bound theorem, but does not assert
general extended-real subharmonic L1-local compactness or a Riesz measure
identity, and does not establish the manuscript's preceding growth bounds.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace V10.SubharmonicHartogs

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [SecondCountableTopology H]

/-- A finite, continuous truncation of a normalized analytic log norm. -/
def clippedLogNorm (L q : ℝ) (f : ℂ → H) (z : ℂ) : ℝ :=
  q⁻¹ * maxLog (L * q) ‖f z‖

omit [NormedSpace ℂ H] [SecondCountableTopology H] in
/-- Zero values of the analytic function give exactly the floor L. -/
theorem clippedLogNorm_of_eq_zero {L q : ℝ} {f : ℂ → H} {z : ℂ}
    (hq : q ≠ 0) (hf : f z = 0) : clippedLogNorm L q f z = L := by
  simp only [clippedLogNorm, hf, norm_zero]
  rw [maxLog_eq_b (Real.exp_pos _).le]
  field_simp

/-- Analyticity supplies actual subharmonicity of each truncated log norm. -/
theorem analytic_clippedLogNorm_subharmonic {L q : ℝ} {f : ℂ → H} {s : Set ℂ}
    (hq : 0 < q) (hf : AnalyticOnNhd ℂ f s) :
    SubharmonicOn (clippedLogNorm L q f) s := by
  exact (hf.maxLog_norm_subharmonicOn (L * q)).const_mul (inv_nonneg.mpr hq.le)

omit [NormedSpace ℂ H] [SecondCountableTopology H] in
/-- An exponential norm bound supplies the corresponding normalized
truncated log bound whenever the truncation floor lies below it. -/
theorem clippedLogNorm_le_of_norm_le {L q d : ℝ} {f : ℂ → H} {z : ℂ}
    (hq : 0 < q) (hLd : L ≤ d) (hf : ‖f z‖ ≤ Real.exp (d * q)) :
    clippedLogNorm L q f z ≤ d := by
  have h := maxLog_le (mul_le_mul_of_nonneg_right hLd hq.le) hf
  change q⁻¹ * maxLog (L * q) ‖f z‖ ≤ d
  calc
    _ ≤ q⁻¹ * (d * q) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hq.le)
    _ = d := by field_simp

/-- Compact Hartogs upper bounds for actual analytic functions, with no
nonvanishing hypothesis. The sequence may be any chosen sampling sequence.
The input pointwise and common bounds are on the actual norms, not an
assumed subharmonic or compactness conclusion. -/
theorem analytic_norm_compact_upper {F : ℕ → ℂ → H} {q : ℕ → ℝ}
    {s k : Set ℂ} {c B : ℝ}
    (hA : ∀ n, AnalyticOnNhd ℂ (F n) s) (hq : ∀ n, 0 < q n)
    (hB : ∀ n z, z ∈ s → ‖F n z‖ ≤ Real.exp (B * q n))
    (hpoint : ∀ z, z ∈ s → ∀ d, c < d →
      ∀ᶠ n in atTop, ‖F n z‖ ≤ Real.exp (d * q n))
    (hk : IsCompact k) (hks : k ⊆ interior s) :
    ∀ d, c < d → ∀ᶠ n in atTop,
      ∀ z, z ∈ k → ‖F n z‖ ≤ Real.exp (d * q n) := by
  let L := min c B
  let u : ℕ → ℂ → ℝ := fun n => clippedLogNorm L (q n) (F n)
  have hs : ∀ n, SubharmonicOn (u n) s := fun n =>
    analytic_clippedLogNorm_subharmonic (hq n) (hA n)
  have hb : ∀ n z, z ∈ s → u n z ≤ B := by
    intro n z hz
    exact clippedLogNorm_le_of_norm_le (hq n) (min_le_right _ _) (hB n z hz)
  have hp : ∀ z, z ∈ s → ∀ d, c < d → ∀ᶠ n in atTop, u n z ≤ d := by
    intro z hz d hd
    exact (hpoint z hz d hd).mono fun n hn =>
      clippedLogNorm_le_of_norm_le (hq n) ((min_le_left _ _).trans hd.le) hn
  intro d hd
  apply (SubharmonicOn.hartogs hs hb hp hk hks d hd).mono
  intro n hn z hz
  have hu := hn z hz
  change (q n)⁻¹ * maxLog (L * q n) ‖F n z‖ ≤ d at hu
  have hmul := mul_le_mul_of_nonneg_left hu (hq n).le
  have hlog : maxLog (L * q n) ‖F n z‖ ≤ d * q n := by
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hq n)), one_mul, mul_one, mul_comm] using hmul
  exact le_of_maxLog_le hlog

/-- The same compact bound in the manuscript's normalized log notation,
restricted to actual nonzero values so that the logarithm retains its meaning.
Apply this to `F n := G (σ n)` and `q n := Q (σ n)` for any subsequence σ;
the norm theorem also covers the zero values without using `Real.log 0`. -/
theorem analytic_logNorm_compact_upper {F : ℕ → ℂ → H} {q : ℕ → ℝ}
    {s k : Set ℂ} {c B : ℝ}
    (hA : ∀ n, AnalyticOnNhd ℂ (F n) s) (hq : ∀ n, 0 < q n)
    (hB : ∀ n z, z ∈ s → ‖F n z‖ ≤ Real.exp (B * q n))
    (hpoint : ∀ z, z ∈ s → ∀ d, c < d →
      ∀ᶠ n in atTop, ‖F n z‖ ≤ Real.exp (d * q n))
    (hk : IsCompact k) (hks : k ⊆ interior s) :
    ∀ d, c < d → ∀ᶠ n in atTop,
      ∀ z, z ∈ k → F n z ≠ 0 → Real.log ‖F n z‖ / q n ≤ d := by
  intro d hd
  apply (analytic_norm_compact_upper hA hq hB hpoint hk hks d hd).mono
  intro n hn z hz hne
  apply (div_le_iff₀ (hq n)).mpr
  have hh := Real.log_le_log (norm_pos_iff.mpr hne) (hn z hz)
  simpa only [Real.log_exp] using hh

#print axioms analytic_clippedLogNorm_subharmonic
#print axioms analytic_norm_compact_upper
#print axioms analytic_logNorm_compact_upper
end V10.SubharmonicHartogs
