import V10.PerronRadial
import V10.PerronNonvanishing
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Open sectors used in the radial Perron theorem

Writing a sector as the exponential image of a horizontal strip keeps the
chosen continuous argument explicit. The geometric facts below in fact hold
without the paper's restriction that the argument interval have width < 2π.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace V10.PerronSector

/-- The image of the logarithmic strip with real part greater than `log R`
and imaginary part in the chosen argument interval `J`. -/
def sector (R : ℝ) (J : Set ℝ) : Set ℂ :=
  Complex.exp '' {w : ℂ | Real.log R < w.re ∧ w.im ∈ J}

theorem sector_isOpen (R : ℝ) {J : Set ℝ} (hJ : IsOpen J) : IsOpen (sector R J) := by
  apply Complex.isOpenMap_exp
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    (hJ.preimage Complex.continuous_im)

theorem sector_isPreconnected (R : ℝ) {J : Set ℝ} (hJ : IsPreconnected J) :
    IsPreconnected (sector R J) := by
  have hstrip : IsPreconnected {w : ℂ | Real.log R < w.re ∧ w.im ∈ J} := by
    have hh := ((isPreconnected_Ioi : IsPreconnected (Ioi (Real.log R))).prod hJ).image
      Complex.equivRealProdCLM.symm Complex.equivRealProdCLM.symm.continuous.continuousOn
    have heq : Complex.equivRealProdCLM.symm '' (Ioi (Real.log R) ×ˢ J) =
        {w : ℂ | Real.log R < w.re ∧ w.im ∈ J} := by
      ext w
      constructor
      · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
        simpa [Complex.equivRealProdCLM_symm_apply] using And.intro ha hb
      · intro hw
        refine ⟨(w.re, w.im), hw, ?_⟩
        simp [Complex.equivRealProdCLM_symm_apply]
    rwa [heq] at hh
  exact hstrip.image Complex.exp Complex.continuous_exp.continuousOn

/-- The standard polar description, with a freely chosen continuous argument. -/
theorem mem_sector_iff {R : ℝ} (hR : 0 < R) {J : Set ℝ} {z : ℂ} :
    z ∈ sector R J ↔ ∃ r > R, ∃ θ ∈ J,
      z = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨Real.exp w.re, ?_, w.im, hw.2, ?_⟩
    · rw [← Real.exp_log hR]
      exact Real.exp_lt_exp.mpr hw.1
    · conv_lhs => rw [← Complex.re_add_im w]
      rw [Complex.exp_add, ← Complex.ofReal_exp]
  · rintro ⟨r, hr, θ, hθ, rfl⟩
    have hr0 : 0 < r := hR.trans hr
    refine ⟨(Real.log r : ℂ) + (θ : ℂ) * Complex.I, ?_, ?_⟩
    · simpa using And.intro (Real.log_lt_log hR hr) hθ
    · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr0]

theorem ray_mem_sector {R r θ : ℝ} {J : Set ℝ}
    (hR : 0 < R) (hr : R < r) (hθ : θ ∈ J) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ sector R J :=
  (mem_sector_iff hR).mpr ⟨r, hr, θ, hθ, rfl⟩

section ODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The full radial spectral classification on an open sector, starting from
a genuinely nonzero solution on the domain. Nonvanishing on each ray and the
real Perron classification are both proved, not additional hypotheses.

Continuity of `A` and convergence on each ray are weaker than the manuscript's
analyticity and uniform convergence on closed subsectors. -/
theorem radial_system_growth {R : ℝ} (hR : 0 < R) {J : Set ℝ}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {Y : ℂ → E}
    (hA : ContinuousOn A (sector R J))
    (hode : ∀ z ∈ sector R J, HasDerivAt Y (A z (Y z)) z)
    (hnonzero : ∃ z ∈ sector R J, Y z ≠ 0)
    (hlim : ∀ θ ∈ J, Tendsto
      (fun r : ℝ => A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) atTop (𝓝 A₀)) :
    ∀ θ ∈ J, ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      Tendsto (fun r : ℝ =>
        Real.log ‖Y ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ / r)
        atTop (𝓝 (μ.val * Complex.exp ((θ : ℂ) * Complex.I)).re) := by
  intro θ hθ
  have hray : ∀ r ≥ R + 1,
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ sector R J := by
    intro r hr
    exact ray_mem_sector hR (by linarith) hθ
  have hne := V10.PerronNonvanishing.nowhere_zero
    (sector_isOpen R hJopen) (sector_isPreconnected R hJconn) hA hode hnonzero
  exact V10.PerronRadial.ray_growth_exponent (Complex.exp_ne_zero _)
    hA hray (hlim θ hθ) hode (hne _ (hray (R + 1) le_rfl))

/-- Lemma 2.2 with the manuscript's uniform-on-closed-subsectors convergence
expressed as uniform convergence on compact sets of angles. Singleton angle
sets give the radial convergence used by the stronger theorem above. -/
theorem lemma_2_2 {R : ℝ} (hR : 0 < R) {J : Set ℝ}
    (hJopen : IsOpen J) (hJconn : IsPreconnected J)
    {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {Y : ℂ → E}
    (hA : ContinuousOn A (sector R J))
    (hode : ∀ z ∈ sector R J, HasDerivAt Y (A z (Y z)) z)
    (hnonzero : ∃ z ∈ sector R J, Y z ≠ 0)
    (hlim : ∀ K : Set ℝ, K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (fun _ => A₀) atTop K) :
    ∀ θ ∈ J, ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
      Tendsto (fun r : ℝ =>
        Real.log ‖Y ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ / r)
        atTop (𝓝 (μ.val * Complex.exp ((θ : ℂ) * Complex.I)).re) := by
  apply radial_system_growth hR hJopen hJconn hA hode hnonzero
  intro θ hθ
  exact (hlim {θ} (singleton_subset_iff.mpr hθ) isCompact_singleton).tendsto_at
    (mem_singleton θ)

end ODE

#print axioms radial_system_growth
#print axioms lemma_2_2

end V10.PerronSector
