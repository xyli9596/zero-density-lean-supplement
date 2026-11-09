import V10.PerronLogLipschitz
import V10.CompactLipschitzLimit

/-!
# Actual vector logarithmic potentials: spectral limits and compact convergence

This is the vector part of the indicator argument. The scalar logarithm at
zeros and its L¹-local convergence are separate, and are not asserted here.
The indicator is a limsup of the actual potentials, not a prescribed spectrum
selection or a structure field containing the desired convergence.
-/

noncomputable section
open Set Filter Module
open scoped Topology NNReal
namespace V10.PerronVectorLimit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def potential (Y : ℂ → E) (R : ℝ) (ζ : ℂ) : ℝ :=
  Real.log ‖Y ((R : ℂ) * ζ)‖ / R

def indicator (Y : ℂ → E) (ζ : ℂ) : ℝ :=
  limsup (fun R => potential Y R ζ) atTop

/-- Actual Perron convergence identifies the limsup and its spectral value
at each admissible complex ray. -/
theorem indicator_ray_limit [FiniteDimensional ℂ E]
    {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {Y : ℂ → E}
    {D : Set ℂ} {ζ : ℂ} {T : ℝ} (hζ : ζ ≠ 0)
    (hA : ContinuousOn A D) (hray : ∀ r ≥ T, (r : ℂ) * ζ ∈ D)
    (hlim : Tendsto (fun r : ℝ => A ((r : ℂ) * ζ)) atTop (𝓝 A₀))
    (hode : ∀ z ∈ D, HasDerivAt Y (A z (Y z)) z)
    (hne : Y ((T : ℂ) * ζ) ≠ 0) :
    Tendsto (fun R => potential Y R ζ) atTop (𝓝 (indicator Y ζ)) ∧
      ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
        indicator Y ζ = (μ.val * ζ).re := by
  obtain ⟨μ, hμ⟩ := V10.PerronRadial.ray_growth_exponent hζ hA hray hlim hode hne
  have heq : indicator Y ζ = (μ.val * ζ).re := hμ.limsup_eq
  refine ⟨?_, μ, heq⟩
  rw [heq]
  exact hμ

omit [NormedSpace ℂ E] in
/-- Positive radial rescaling gives the exact homogeneity of the limiting
vector indicator, whenever the actual potential has a limit at the point. -/
theorem indicator_pos_homogeneous {Y : ℂ → E} {ζ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hlim : Tendsto (fun R => potential Y R ζ) atTop (𝓝 (indicator Y ζ))) :
    indicator Y ((ρ : ℂ) * ζ) = ρ * indicator Y ζ := by
  have hc : Tendsto (fun R : ℝ => R * ρ) atTop atTop :=
    tendsto_id.atTop_mul_const hρ
  have hh := (hlim.comp hc).const_mul ρ
  have heq : (fun R : ℝ => ρ * potential Y (R * ρ) ζ) =ᶠ[atTop]
      (fun R => potential Y R ((ρ : ℂ) * ζ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    simp only [potential, Complex.ofReal_mul, mul_assoc]
    field_simp
  exact (hh.congr' heq).limsup_eq

/-- The actual ODE and a uniform coefficient bound, rather than an assumed
equicontinuity statement, supply a common Lipschitz constant for the scaled
logarithmic vector potentials. -/
theorem eventually_lipschitz_potential {D : Set ℂ} (hD : Convex ℝ D)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} {M : ℝ≥0}
    (hode : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, HasDerivAt Y
      (A ((R : ℂ) * ζ) (Y ((R : ℂ) * ζ))) ((R : ℂ) * ζ))
    (hA : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, ‖A ((R : ℂ) * ζ)‖ ≤ M)
    (hne : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, Y ((R : ℂ) * ζ) ≠ 0) :
    ∀ᶠ R : ℝ in atTop, LipschitzOnWith M (potential Y R) D := by
  filter_upwards [hode, hA, hne, eventually_gt_atTop (0 : ℝ)] with R ho hA hn hR
  apply LipschitzOnWith.of_dist_le_mul
  intro w hw z hz
  simpa only [potential, Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using
    PerronLogLipschitz.scaled_log_norm_sub_le hD hR ho hA hz hw (hn z hz)

/-- On any compact subset of a convex neighborhood, Perron pointwise limits
and the actual ODE bound give uniform convergence of the vector potentials.
The limit is Lipschitz and continuous on the neighborhood itself. -/
theorem vector_potential_compact_limit {D K : Set ℂ} (hD : Convex ℝ D)
    (hK : IsCompact K) (hKD : K ⊆ D)
    {A : ℂ → E →L[ℂ] E} {Y : ℂ → E} {M : ℝ≥0}
    (hode : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, HasDerivAt Y
      (A ((R : ℂ) * ζ) (Y ((R : ℂ) * ζ))) ((R : ℂ) * ζ))
    (hA : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, ‖A ((R : ℂ) * ζ)‖ ≤ M)
    (hne : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, Y ((R : ℂ) * ζ) ≠ 0)
    (hpoint : ∀ ζ ∈ D, Tendsto (fun R => potential Y R ζ) atTop (𝓝 (indicator Y ζ))) :
    TendstoUniformlyOn (potential Y) (indicator Y) atTop K ∧
      LipschitzOnWith M (indicator Y) D ∧ ContinuousOn (indicator Y) D := by
  have hLip := eventually_lipschitz_potential hD hode hA hne
  have hLipK := hLip.mono fun _ h => h.mono hKD
  exact ⟨CompactLipschitzLimit.tendstoUniformlyOn_of_pointwise_limit hK hLipK
      (fun ζ hζ => hpoint ζ (hKD hζ)),
    CompactLipschitzLimit.lipschitzOnWith_of_pointwise_limit hLip hpoint,
    CompactLipschitzLimit.continuousOn_of_pointwise_limit hLip hpoint⟩

/-- An actual ODE endpoint: spectral pointwise limits and compact uniform
convergence are both derived. On a convex scaled neighborhood, the hypotheses
only require domain inclusion, coefficient convergence and a uniform
coefficient bound, together with the actual nonvanishing differential equation.
No indicator selection or convergence of potentials is an input. -/
theorem actual_vector_compact_limit [FiniteDimensional ℂ E]
    {Ω D K : Set ℂ} (hD : Convex ℝ D) (hK : IsCompact K) (hKD : K ⊆ D)
    (hDzero : ∀ ζ ∈ D, ζ ≠ 0)
    {A : ℂ → E →L[ℂ] E} {A₀ : E →L[ℂ] E} {Y : ℂ → E} {M : ℝ≥0}
    (hcont : ContinuousOn A Ω)
    (hode : ∀ z ∈ Ω, HasDerivAt Y (A z (Y z)) z)
    (hne : ∀ z ∈ Ω, Y z ≠ 0)
    (hmap : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, (R : ℂ) * ζ ∈ Ω)
    (hbound : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, ‖A ((R : ℂ) * ζ)‖ ≤ M)
    (hlim : ∀ ζ ∈ D, Tendsto (fun R : ℝ => A ((R : ℂ) * ζ)) atTop (𝓝 A₀)) :
    TendstoUniformlyOn (potential Y) (indicator Y) atTop K ∧
      LipschitzOnWith M (indicator Y) D ∧ ContinuousOn (indicator Y) D ∧
      ∀ ζ ∈ D, ∃ μ : Module.End.Eigenvalues (A₀.toLinearMap : Module.End ℂ E),
        indicator Y ζ = (μ.val * ζ).re := by
  obtain ⟨T, hT⟩ := eventually_atTop.1 hmap
  have hray (ζ : ℂ) (hζ : ζ ∈ D) := indicator_ray_limit (hDzero ζ hζ) hcont
    (fun R hR => hT R hR ζ hζ) (hlim ζ hζ) hode (hne _ (hT T le_rfl ζ hζ))
  have ho : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, HasDerivAt Y
      (A ((R : ℂ) * ζ) (Y ((R : ℂ) * ζ))) ((R : ℂ) * ζ) :=
    hmap.mono fun _ h ζ hζ => hode _ (h ζ hζ)
  have hn : ∀ᶠ R : ℝ in atTop, ∀ ζ ∈ D, Y ((R : ℂ) * ζ) ≠ 0 :=
    hmap.mono fun _ h ζ hζ => hne _ (h ζ hζ)
  have hh := vector_potential_compact_limit hD hK hKD ho hbound hn
    (fun ζ hζ => (hray ζ hζ).1)
  exact ⟨hh.1, hh.2.1, hh.2.2, fun ζ hζ => (hray ζ hζ).2⟩

#print axioms indicator_ray_limit
#print axioms indicator_pos_homogeneous
#print axioms vector_potential_compact_limit
#print axioms actual_vector_compact_limit
end V10.PerronVectorLimit
