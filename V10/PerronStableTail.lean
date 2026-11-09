import V10.PerronStableSubspaceCoordinates
import V10.PerronDichotomyBasis
import V10.PerronStableDimension
import V10.PerronStableFlowUniqueness

/-! Actual asymptotically constant ODE coefficients are put into the uniformly
small mixed-Volterra setting using a genuine scaled Jordan basis. -/
namespace V10.PerronStableSubspace
open Set Filter Module
open scoped Topology Matrix BoundedContinuousFunction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E]
open V10.PerronDichotomyBasis

/-- The spectral gap and the smallness threshold are proved compatible. -/
lemma exists_contraction_threshold (δ : ℝ) :
    ∃ η : ℝ, 0 < η ∧ decayMass δ * η < 1 := by
  let η : ℝ := (2 * (decayMass δ + 1))⁻¹
  have hm := decayMass_nonneg δ
  have hp : 0 < 2 * (decayMass δ + 1) := by positivity
  refine ⟨η, inv_pos.mpr hp, ?_⟩
  have he : (2 * (decayMass δ + 1)) * η = 1 := mul_inv_cancel₀ hp.ne'
  have hη : 0 < η := inv_pos.mpr hp
  nlinarith

/-- Actual tail coordinates for an asymptotically constant coefficient. The
matrix identity, small operator remainder, and exact stable count are all
conclusions from the true spectrum and convergence of the coefficient. -/
theorem exists_small_tail_coordinates {A : ℝ → E →L[ℂ] E} {A₀ : E →L[ℂ] E}
    {T₀ γ : ℝ} (μ : ℂ)
    (hA : ContinuousOn A (Ici T₀)) (hlim : Tendsto A atTop (𝓝 A₀))
    (hμ : Module.End.HasEigenvalue (A₀.toLinearMap : End ℂ E) μ) (hμre : γ < μ.re)
    (hrest : ∀ a : Module.End.Eigenvalues (A₀.toLinearMap : End ℂ E), a.val ≠ μ → a.val.re < γ) :
    ∃ T ≥ T₀, ∃ δ : ℝ, ∃ η : ℝ, 0 < δ ∧ 0 < η ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι ℂ E)
        (mode : ι → Bool) (lam : ι → ℂ)
        (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)),
        (∀ i, if mode i then (lam i).re ≤ -δ else δ ≤ (lam i).re) ∧
        Continuous R ∧ (∀ t, ‖R t‖ ≤ η) ∧ decayMass δ * η < 1 ∧
        Fintype.card {i : ι // mode i = true} =
          finrank ℂ E - (A₀.toLinearMap : End ℂ E).charpoly.rootMultiplicity μ ∧
        (∀ t : Ici T, ∀ y : ι → ℂ,
          ((basisCoordinates b).arrowCongr (basisCoordinates b)
            (A t - (γ : ℂ) • ContinuousLinearMap.id ℂ E)) y =
          fun i => lam i * y i + R t y i) := by
  classical
  obtain ⟨δ, hδ, hc⟩ := exists_stable_coordinates (A₀.toLinearMap : End ℂ E) γ μ hμ hμre hrest
  obtain ⟨η, hη, hsmall⟩ := exists_contraction_threshold δ
  obtain ⟨ι, fι, dι, b, mode, lam, N, hmat, hgap, hN, hcount⟩ := hc (η / 2) (by positivity)
  let _ := fι
  let _ := dι
  let e := basisCoordinates b
  let B : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ) := fun t => e.arrowCongr e (A t - A₀)
  have hBlim : Tendsto B atTop (𝓝 0) :=
    conjugated_perturbation_tendsto e (by simpa using hlim.sub_const A₀)
  have hevent : ∀ᶠ t in atTop, ‖B t‖ < η / 2 := by
    have hh := hBlim.eventually (Metric.ball_mem_nhds 0 (show 0 < η / 2 by positivity))
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hevent
  let T := max T₀ T₁
  let R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ) := fun t =>
    (Matrix.toLin' N).toContinuousLinearMap + B t
  have hRc : Continuous R := by
    have hAc : Continuous (fun t : Ici T => A t) :=
      hA.comp_continuous continuous_subtype_val (fun t => (le_max_left T₀ T₁).trans t.property)
    dsimp [R, B]
    exact continuous_const.add ((e.arrowCongr e).continuous.comp (hAc.sub continuous_const))
  have hRb : ∀ t : Ici T, ‖R t‖ ≤ η := by
    intro t
    apply (norm_add_le _ _).trans
    have hh := (hT₁ t ((le_max_right T₀ T₁).trans t.property)).le
    linarith
  refine ⟨T, le_max_left _ _, δ, η, hδ, hη, ι, fι, dι, b, mode, lam, R,
    hgap, hRc, hRb, hsmall, hcount, ?_⟩
  intro t y
  have hconst : (e.arrowCongr e (A₀ - (γ : ℂ) • ContinuousLinearMap.id ℂ E)) y =
      fun i => lam i * y i + ((Matrix.toLin' N).toContinuousLinearMap y) i := by
    rw [conjugate_apply_eq_toMatrix]
    change (LinearMap.toMatrix b b (A₀.toLinearMap - (γ : ℂ) • 1)) *ᵥ y = _
    rw [hmat, Matrix.add_mulVec]
    ext i
    simp only [Pi.add_apply, Matrix.mulVec_diagonal]
    rfl
  have hop : e.arrowCongr e (A t - (γ : ℂ) • ContinuousLinearMap.id ℂ E) =
      e.arrowCongr e (A₀ - (γ : ℂ) • ContinuousLinearMap.id ℂ E) + B t := by
    dsimp [B]
    rw [← map_add]
    congr 1
    abel
  rw [hop, add_apply, hconst]
  ext i
  change lam i * y i + ((Matrix.toLin' N).toContinuousLinearMap y) i + B t y i =
    lam i * y i + (((Matrix.toLin' N).toContinuousLinearMap y) i + B t y i)
  ring

#print axioms exists_small_tail_coordinates
end
end V10.PerronStableSubspace
