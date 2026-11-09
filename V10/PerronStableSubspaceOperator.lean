import V10.PerronStableSubspace

/-! Actual mixed integral operator with a uniform smallness bound, without an
L1 assumption on the perturbation. -/
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

def integralVector (u : Ici T →ᵇ (ι → ℂ)) (r : Ici T) (i : ι) : ℂ :=
  ∫ s : ℝ, kernel T (mode i) (lam i) r s *
    (R (clamp T s) (u (clamp T s))) i

include hη hgap hsmallR in
lemma integrand_bound (u : Ici T →ᵇ (ι → ℂ)) (r : Ici T) (i : ι) (s : ℝ) :
    ‖kernel T (mode i) (lam i) r s * (R (clamp T s) (u (clamp T s))) i‖ ≤
      decay δ r s * (η * ‖u‖) := by
  calc
    _ = ‖kernel T (mode i) (lam i) r s‖ * ‖(R (clamp T s) (u (clamp T s))) i‖ := norm_mul _ _
    _ ≤ decay δ r s * (η * ‖u‖) := by
      apply mul_le_mul (kernel_bound _ _ (hgap i) r s) ?_ (norm_nonneg _) (decay_nonneg _ _ _)
      calc
        _ ≤ ‖R (clamp T s) (u (clamp T s))‖ := norm_le_pi_norm _ _
        _ ≤ ‖R (clamp T s)‖ * ‖u (clamp T s)‖ := (R _).le_opNorm _
        _ ≤ η * ‖u‖ := mul_le_mul (hsmallR _) (u.norm_coe_le_norm _)
          (norm_nonneg _) hη

include hR in
lemma integrand_measurable (u : Ici T →ᵇ (ι → ℂ)) (r : Ici T) (i : ι) :
    AEStronglyMeasurable (fun s : ℝ => kernel T (mode i) (lam i) r s *
      (R (clamp T s) (u (clamp T s))) i) := by
  have hc : Continuous (fun s : ℝ => (R (clamp T s) (u (clamp T s))) i) := by
    have hcl := continuous_clamp T
    fun_prop
  exact ((kernel_measurable T (mode i) (lam i) r).mul hc.measurable).aestronglyMeasurable

include hδ hη hgap hR hsmallR in
lemma integrand_integrable (u : Ici T →ᵇ (ι → ℂ)) (r : Ici T) (i : ι) :
    Integrable (fun s : ℝ => kernel T (mode i) (lam i) r s *
      (R (clamp T s) (u (clamp T s))) i) := by
  exact ((integrable_decay hδ r).mul_const (η * ‖u‖)).mono'
    (integrand_measurable T mode lam R hR u r i)
    (ae_of_all _ (integrand_bound T δ η hη mode lam hgap R hsmallR u r i))

include hδ hη hgap hR hsmallR in
lemma integralVector_continuous (u : Ici T →ᵇ (ι → ℂ)) :
    Continuous (integralVector T mode lam R u) := by
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro r
  apply continuousAt_of_dominated
    (bound := fun s => (Real.exp δ * decay δ r s) * (η * ‖u‖))
    (Eventually.of_forall fun t => integrand_measurable T mode lam R hR u t i)
    ?_ (((integrable_decay hδ r).const_mul (Real.exp δ)).mul_const (η * ‖u‖))
  · filter_upwards [(volume : Measure ℝ).ae_ne (r : ℝ)] with s hs
    exact (kernel_continuousAt T (mode i) (lam i) r s hs).mul continuousAt_const
  · filter_upwards [Metric.ball_mem_nhds r (by norm_num : (0 : ℝ) < 1)] with t ht
    apply ae_of_all
    intro s
    apply (integrand_bound T δ η hη mode lam hgap R hsmallR u t i s).trans
    apply mul_le_mul_of_nonneg_right (decay_local_bound hδ.le ?_) (mul_nonneg hη (norm_nonneg _))
    exact (by simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using ht :
      |(t : ℝ) - (r : ℝ)| < 1).le

include hδ hη hgap hsmallR in
lemma integralVector_bound (u : Ici T →ᵇ (ι → ℂ)) (r : Ici T) :
    ‖integralVector T mode lam R u r‖ ≤ (decayMass δ * η) * ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (decayMass_nonneg δ) hη) (norm_nonneg _))).mpr
  intro i
  calc
    _ ≤ ∫ s : ℝ, decay δ r s * (η * ‖u‖) :=
      norm_integral_le_of_norm_le ((integrable_decay hδ r).mul_const (η * ‖u‖))
        (ae_of_all _ (integrand_bound T δ η hη mode lam hgap R hsmallR u r i))
    _ = _ := by rw [integral_mul_const, integral_decay]; ring

def integralOperator (u : Ici T →ᵇ (ι → ℂ)) : Ici T →ᵇ (ι → ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (integralVector T mode lam R u)
    (integralVector_continuous T δ η hδ hη mode lam hgap R hR hsmallR u)
    ((decayMass δ * η) * ‖u‖)
    (integralVector_bound T δ η hδ hη mode lam hgap R hsmallR u)

include hδ hη hgap hR hsmallR in
lemma integralVector_sub (u v : Ici T →ᵇ (ι → ℂ)) (r : Ici T) :
    integralVector T mode lam R (u - v) r =
      integralVector T mode lam R u r - integralVector T mode lam R v r := by
  ext i
  simp only [integralVector, BoundedContinuousFunction.sub_apply, map_sub, Pi.sub_apply, mul_sub]
  exact integral_sub
    (integrand_integrable T δ η hδ hη mode lam hgap R hR hsmallR u r i)
    (integrand_integrable T δ η hδ hη mode lam hgap R hR hsmallR v r i)

lemma integralOperator_lipschitz (u v : Ici T →ᵇ (ι → ℂ)) :
    ‖integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u -
      integralOperator T δ η hδ hη mode lam hgap R hR hsmallR v‖ ≤
      (decayMass δ * η) * ‖u - v‖ := by
  apply (BoundedContinuousFunction.norm_le
    (mul_nonneg (mul_nonneg (decayMass_nonneg δ) hη) (norm_nonneg _))).mpr
  intro r
  change ‖integralVector T mode lam R u r - integralVector T mode lam R v r‖ ≤ _
  rw [← integralVector_sub T δ η hδ hη mode lam hgap R hR hsmallR u v r]
  exact integralVector_bound T δ η hδ hη mode lam hgap R hsmallR (u - v) r

/-- Genuine existence and uniqueness for the uniform-small mixed integral equation. -/
theorem exists_unique_fixed_point (c : Ici T →ᵇ (ι → ℂ))
    (hsmall : decayMass δ * η < 1) :
    ∃! u : Ici T →ᵇ (ι → ℂ), u = c +
      integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u := by
  let a : NNReal := ⟨decayMass δ * η, mul_nonneg (decayMass_nonneg δ) hη⟩
  have ha : a < 1 := hsmall
  have hF : ∀ u v : Ici T →ᵇ (ι → ℂ),
      ‖(c + integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u) -
        (c + integralOperator T δ η hδ hη mode lam hgap R hR hsmallR v)‖ ≤
        (a : ℝ) * ‖u - v‖ := by
    intro u v
    rw [add_sub_add_left_eq_sub]
    exact integralOperator_lipschitz T δ η hδ hη mode lam hgap R hR hsmallR u v
  obtain ⟨u, hu, huniq⟩ := CRGRay.fixed_point_of_norm_bound
    (fun u => c + integralOperator T δ η hδ hη mode lam hgap R hR hsmallR u) a ha hF
  exact ⟨u, hu.symm, fun v hv => huniq v hv.symm⟩

end V10.PerronStableSubspace
