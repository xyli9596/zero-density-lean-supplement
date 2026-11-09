import V10.ProjectionLemma43

/-! The standard physical windows are actual invertible real affine maps. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace V10.ProjectionPhysicalWindows
open ProjectionRowFamily ProjectionLemma43
set_option backward.isDefEq.respectTransparency false

/-- The linear part of `(ξ,η) ↦ ω⁻¹(R+ξ+i√Rη)`. Positivity of R
is the actual reason that the transverse scaling is invertible. -/
def physicalLinear (R : ℝ) (ω : ℂ) (hR : 0 < R) (hω : ω ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] ℂ :=
  (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.mk0 (Real.sqrt R) (Real.sqrt_pos.mpr hR).ne'))).trans
    Complex.equivRealProdCLM.symm).trans
      ((ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0 ω⁻¹ (inv_ne_zero hω))).restrictScalars ℝ)

theorem physicalLinear_apply (R : ℝ) (ω : ℂ) (hR : 0 < R) (hω : ω ≠ 0)
    (z : ℝ × ℝ) :
    physicalLinear R ω hR hω z =
      ω⁻¹ * ((z.1 : ℂ) + Complex.I * (Real.sqrt R : ℂ) * (z.2 : ℂ)) := by
  simp [physicalLinear, ContinuousLinearEquiv.trans_apply,
    Complex.equivRealProdCLM_symm_apply, mul_comm, mul_left_comm]

theorem physicalWindow_eq (R : ℝ) (ω : ℂ) (hR : 0 < R) (hω : ω ≠ 0)
    (z : ℝ × ℝ) :
    physicalLinear R ω hR hω z + ω⁻¹ * (R : ℂ) =
      ω⁻¹ * ((R : ℂ) + (z.1 : ℂ) + Complex.I * (Real.sqrt R : ℂ) * (z.2 : ℂ)) := by
  rw [physicalLinear_apply]
  ring

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [Nonempty Ω]

/-- The complete exceptional cone of Lemma 4.3 applies to the exact
anisotropic physical windows used later in the manuscript. -/
theorem physical_window_projection {f : ι → ℂ → ℂ}
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) univ) (hi : LinearIndependent ℂ f)
    (hn : ∀ z, ∃ j, f j z ≠ 0)
    (ω : Ω → ℂ) (hω : ∀ dir, ω dir ≠ 0)
    (R : ℕ → ℝ) (hR : ∀ m, 0 < R m)
    {Q : ℕ → ℝ} (hQ : ∀ m, 0 < Q m) (hQs : Summable (fun m => (Q m)⁻¹)) :
    ∃ (Ψ : EuclideanSpace ℂ ι → EReal) (κ : ℝ),
      ERealPlurisubharmonic.Plurisubharmonic Ψ ∧ 0 < κ ∧
      ExceptionalCone.LogHomogeneous Ψ κ ∧ (∃ c, Ψ c ≠ ⊥) ∧
      IsCompletePluripolar {c | Ψ c = ⊥} ∧
      (∀ c, ∀ α : ℂ, Ψ c = ⊥ → Ψ (α • c) = ⊥) ∧
      (∀ c, Ψ c ≠ ⊥ → ∀ dir : Ω, ∀ K : Set (ℝ × ℝ), IsCompact K →
        Tendsto (fun m => (Q m)⁻¹ * ∫ z in K,
          |Real.log (‖∑ j, f j ((ω dir)⁻¹ * ((R m : ℂ) + (z.1 : ℂ) +
              Complex.I * (Real.sqrt (R m) : ℂ) * (z.2 : ℂ))) * c j‖ /
            ‖rowVector f ((ω dir)⁻¹ * ((R m : ℂ) + (z.1 : ℂ) +
              Complex.I * (Real.sqrt (R m) : ℂ) * (z.2 : ℂ)))‖)|)
          atTop (𝓝 0)) := by
  simpa only [physicalWindow_eq] using lemma_4_3 hf hi hn
    (fun dir m => physicalLinear (R m) (ω dir) (hR m) (hω dir))
    (fun dir m => (ω dir)⁻¹ * (R m : ℂ)) hQ hQs

#print axioms physicalWindow_eq
#print axioms physical_window_projection
end V10.ProjectionPhysicalWindows
