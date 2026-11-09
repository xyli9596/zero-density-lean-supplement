import V10.PerronStableSubspaceOperator

/-! Stable forcing, linearity, and the initial stable projection for the actual
uniform-small mixed integral equation. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
namespace V10.PerronStableSubspace
variable {ι : Type*} [Fintype ι]
variable (T δ η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
variable (mode : ι → Bool) (lam : ι → ℂ)
variable (hgap : ∀ i, if mode i then (lam i).re ≤ -δ else δ ≤ (lam i).re)
variable (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
variable (hsmallR : ∀ s, ‖R s‖ ≤ η)

/-- The proved integral operator is complex-linear. -/
def integralLinear : (Ici T →ᵇ (ι → ℂ)) →ₗ[ℂ] (Ici T →ᵇ (ι → ℂ)) where
  toFun := integralOperator T δ η hδ hη mode lam hgap R hR hsmallR
  map_add' u v := by
    ext r i
    change integralVector T mode lam R (u + v) r i =
      integralVector T mode lam R u r i + integralVector T mode lam R v r i
    simp only [integralVector, BoundedContinuousFunction.add_apply, map_add,
      Pi.add_apply, mul_add]
    exact integral_add
      (integrand_integrable T δ η hδ hη mode lam hgap R hR hsmallR u r i)
      (integrand_integrable T δ η hδ hη mode lam hgap R hR hsmallR v r i)
  map_smul' c u := by
    ext r i
    change integralVector T mode lam R (c • u) r i = c * integralVector T mode lam R u r i
    simp only [integralVector, BoundedContinuousFunction.smul_apply, map_smul,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [← mul_assoc, mul_comm _ c, mul_assoc]
    exact integral_const_mul c _

def forcingVector (v : ι → ℂ) (r : Ici T) (i : ι) : ℂ :=
  if mode i then Complex.exp (lam i * ((r : ℝ) - T)) * v i else 0

omit [Fintype ι] in
lemma forcingVector_continuous (v : ι → ℂ) :
    Continuous (forcingVector T mode lam v) := by
  apply continuous_pi
  intro i
  cases hi : mode i <;> simp only [forcingVector, hi, Bool.false_eq_true, ↓reduceIte]
  · exact continuous_const
  · fun_prop

include hδ hgap in
lemma forcingVector_bound (v : ι → ℂ) (r : Ici T) :
    ‖forcingVector T mode lam v r‖ ≤ ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
  intro i
  cases hi : mode i
  · simp [forcingVector, hi]
  · have he : ‖Complex.exp (lam i * ((r : ℝ) - T))‖ ≤ 1 := by
      rw [Complex.norm_exp, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_im, sub_self, mul_zero, sub_zero]
      have hh := hgap i
      simp only [hi, ↓reduceIte] at hh
      have hr : 0 ≤ (r : ℝ) - T := sub_nonneg.mpr r.property
      nlinarith
    calc
      _ = ‖Complex.exp (lam i * ((r : ℝ) - T))‖ * ‖v i‖ := by
        simp only [forcingVector, hi, ↓reduceIte, norm_mul]
      _ ≤ 1 * ‖v i‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ ≤ ‖v‖ := by simpa using norm_le_pi_norm v i

def forcing (v : ι → ℂ) : Ici T →ᵇ (ι → ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup (forcingVector T mode lam v)
    (forcingVector_continuous T mode lam v) ‖v‖
    (forcingVector_bound T δ hδ mode lam hgap v)

lemma forcing_apply (v : ι → ℂ) (r : Ici T) (i : ι) :
    forcing T δ hδ mode lam hgap v r i =
      if mode i then Complex.exp (lam i * ((r : ℝ) - T)) * v i else 0 := rfl

def forcingLinear : (ι → ℂ) →ₗ[ℂ] (Ici T →ᵇ (ι → ℂ)) where
  toFun := forcing T δ hδ mode lam hgap
  map_add' u v := by
    ext r i
    change forcingVector T mode lam (u + v) r i =
      forcingVector T mode lam u r i + forcingVector T mode lam v r i
    cases hi : mode i <;> simp [forcingVector, hi, mul_add]
  map_smul' c v := by
    ext r i
    change forcingVector T mode lam (c • v) r i = c * forcingVector T mode lam v r i
    cases hi : mode i <;> simp [forcingVector, hi, mul_left_comm]

lemma kernel_initial_forward (lam : ℂ) (s : ℝ) (hs : s ≠ T) :
    kernel T true lam ⟨T, by exact le_refl T⟩ s = 0 := by
  unfold kernel MixedVolterra.kernel
  simp only [↓reduceIte]
  split_ifs with hTs hsT
  · exact (hs (le_antisymm hsT hTs)).elim
  · rfl
  · rfl

lemma integralVector_initial_forward (u : Ici T →ᵇ (ι → ℂ)) (i : ι) (hi : mode i = true) :
    integralVector T mode lam R u ⟨T, by exact le_refl T⟩ i = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [(volume : Measure ℝ).ae_ne T] with s hs
  simp only [hi, kernel_initial_forward T (lam i) s hs, zero_mul, Pi.zero_apply]

/-- The fixed-point equation recovers precisely the stable initial coordinates. -/
theorem fixed_point_initial_stable (v : ι → ℂ) (u : Ici T →ᵇ (ι → ℂ))
    (hu : u = forcing T δ hδ mode lam hgap v +
      integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u)
    (i : ι) (hi : mode i = true) : u ⟨T, by exact le_refl T⟩ i = v i := by
  have hh := congrArg (fun w : Ici T →ᵇ (ι → ℂ) => w ⟨T, by exact le_refl T⟩ i) hu
  change u ⟨T, by exact le_refl T⟩ i = forcingVector T mode lam v ⟨T, by exact le_refl T⟩ i +
    integralVector T mode lam R u ⟨T, by exact le_refl T⟩ i at hh
  simpa [forcingVector, hi, integralVector_initial_forward T mode lam R u i hi] using hh

/-- Every stable forcing admits a unique actual bounded continuous fixed point. -/
theorem exists_unique_stable_fixed_point (hsmall : decayMass δ * η < 1) (v : ι → ℂ) :
    ∃! u : Ici T →ᵇ (ι → ℂ), u = forcing T δ hδ mode lam hgap v +
      integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u :=
  exists_unique_fixed_point T δ η hδ hη mode lam hgap R hR hsmallR
    (forcing T δ hδ mode lam hgap v) hsmall

end V10.PerronStableSubspace
