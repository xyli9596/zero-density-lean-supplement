import V10.PluriPotentialSeries
import Mathlib.Tactic

/-!
# Extended-real plurisubharmonic potentials

The disk average of an extended-real function bounded above by a finite
constant is defined by the Lebesgue integral of its nonnegative deficit.
This retains negative-infinite values. The plurisubharmonic predicate below
requires the actual disk inequality on each complex affine line, as well as
upper semicontinuity and absence of positive-infinite values.

Local representations as a finite constant minus a genuine nonnegative
plurisuperharmonic function imply this predicate. The proof transfers the
actual deficit integrals; local representations are not the definition.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

namespace V10.ERealPlurisubharmonic
open PluriPotentialSeries

/-- The nonnegative deficit below a finite upper bound. -/
def deficit {X : Type*} (C : ℝ) (f : X → EReal) (x : X) : ℝ≥0∞ :=
  ((C : EReal) - f x).toENNReal

/-- The genuine area-normalized extended disk integral, expressed through
a finite upper bound. Infinite deficit gives average negative infinity. -/
def diskMean (C : ℝ) (f : ℂ → EReal) (c : ℂ) (r : ℝ) : EReal :=
  (C : EReal) -
    (ENNReal.ofReal (Real.pi * r ^ 2)⁻¹ *
      ∫⁻ z in closedBall c r, deficit C f z : ℝ≥0∞)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Extended-real plurisubharmonicity, allowing negative-infinite poles.
Every disk on every complex affine line has a finite upper bound and obeys
the actual area submean inequality. An identically negative-infinite line
is allowed, as in the usual pluripotential convention. -/
structure Plurisubharmonic (Ψ : E → EReal) : Prop where
  upperSemicontinuous : UpperSemicontinuous Ψ
  ne_top : ∀ x, Ψ x ≠ ⊤
  submean : ∀ (a b : E) (c : ℂ) (r : ℝ), 0 < r → ∃ C : ℝ,
    (∀ z ∈ closedBall c r, Ψ (a + z • b) ≤ (C : EReal)) ∧
    AEMeasurable (fun z : ℂ => deficit C Ψ (a + z • b))
      (volume.restrict (closedBall c r)) ∧
    Ψ (a + c • b) ≤ diskMean C (fun z : ℂ => Ψ (a + z • b)) c r

private theorem coe_sub_coe_sub (C : ℝ) (d : ℝ≥0∞) :
    (C : EReal) - ((C : EReal) - (d : EReal)) = (d : EReal) := by
  induction d using ENNReal.recTopCoe with
  | top => simp
  | coe d =>
    simp only [EReal.coe_nnreal_eq_coe_real, ← EReal.coe_sub]
    congr 1
    ring

private theorem coe_sub_le (C : ℝ) (d : ℝ≥0∞) :
    (C : EReal) - (d : EReal) ≤ (C : EReal) := by
  simpa using EReal.sub_le_sub (le_refl (C : EReal)) (EReal.coe_ennreal_nonneg d)

private theorem continuous_coe_sub (C : ℝ) :
    Continuous (fun d : ℝ≥0∞ => (C : EReal) - (d : EReal)) := by
  apply continuous_iff_continuousAt.mpr
  intro d
  change ContinuousAt (fun t : ℝ≥0∞ => (C : EReal) + -(t : EReal)) d
  have hpair : ContinuousAt (fun t : ℝ≥0∞ => ((C : EReal), -(t : EReal))) d :=
    (continuous_const.prodMk continuous_coe_ennreal_ereal.neg).continuousAt
  exact (EReal.continuousAt_add (p := ((C : EReal), -(d : EReal)))
    (Or.inl (EReal.coe_ne_top C)) (Or.inl (EReal.coe_ne_bot C))).comp
      (f := fun t : ℝ≥0∞ => ((C : EReal), -(t : EReal))) hpair

omit [NormedSpace ℂ E] in
private theorem upperSemicontinuousOn_coe_sub {D : E → ℝ≥0∞} {U : Set E}
    (C : ℝ) (hD : LowerSemicontinuousOn D U) :
    UpperSemicontinuousOn (fun x => (C : EReal) - (D x : EReal)) U := by
  apply (continuous_coe_sub C).comp_lowerSemicontinuousOn_antitone hD
  intro x y hxy
  exact EReal.sub_le_sub le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxy)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- The local deficit is exactly the actual superharmonic representative,
including at its infinite poles. -/
theorem deficit_eq_of_representation {Ψ : E → EReal} {D : E → ℝ≥0∞}
    {C : ℝ} {x : E} (h : Ψ x = (C : EReal) - (D x : EReal)) :
    deficit C Ψ x = D x := by
  rw [deficit, h, coe_sub_coe_sub, EReal.toENNReal_coe]

/-- Representations on every centered ball produce a literal extended-real
PSH function. Compactness of the affine disk chooses one common local
representative, whose measurable integral and true supermean inequality
are then transported to the deficit disk mean. -/
theorem plurisubharmonic_of_ball_representations {Ψ : E → EReal}
    (hlocal : ∀ B : ℝ, 1 < B → ∃ (C : ℝ) (D : E → ℝ≥0∞),
      PlurisuperharmonicOn D (ball (0 : E) B) ∧
      ∀ x ∈ ball (0 : E) B, Ψ x = (C : EReal) - (D x : EReal)) :
    Plurisubharmonic Ψ := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    have hB : (1 : ℝ) < ‖x‖ + 2 := by linarith [norm_nonneg x]
    have hx : x ∈ ball (0 : E) (‖x‖ + 2) := by simp
    obtain ⟨C, D, hD, heq⟩ := hlocal _ hB
    have hu := upperSemicontinuousOn_coe_sub C hD.lowerSemicontinuousOn x hx y
      (by change (C : EReal) - (D x : EReal) < y; rwa [← heq x hx])
    rw [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hx)] at hu
    filter_upwards [hu, isOpen_ball.mem_nhds hx] with z hz hzB
    rwa [heq z hzB]
  · intro x
    have hB : (1 : ℝ) < ‖x‖ + 2 := by linarith [norm_nonneg x]
    have hx : x ∈ ball (0 : E) (‖x‖ + 2) := by simp
    obtain ⟨C, D, _, heq⟩ := hlocal _ hB
    rw [heq x hx]
    exact ne_of_lt ((coe_sub_le C (D x)).trans_lt (EReal.coe_lt_top C))
  · intro a b c r hr
    have hcont : Continuous (fun z : ℂ => a + z • b) :=
      continuous_const.add (continuous_id.smul continuous_const)
    obtain ⟨B, hB, hball⟩ :=
      ((isCompact_closedBall c r).image hcont).isBounded.subset_ball_lt 1 (0 : E)
    obtain ⟨C, D, hD, heq⟩ := hlocal B hB
    have hs : closedBall c r ⊆ {z : ℂ | a + z • b ∈ ball (0 : E) B} := by
      intro z hz
      exact hball ⟨z, hz, rfl⟩
    have hc : a + c • b ∈ ball (0 : E) B :=
      hs (mem_closedBall_self hr.le)
    have hdef : ∀ z ∈ closedBall c r,
        deficit C Ψ (a + z • b) = D (a + z • b) :=
      fun z hz => deficit_eq_of_representation (heq _ (hs hz))
    have hae : (fun z : ℂ => deficit C Ψ (a + z • b)) =ᵐ[
        volume.restrict (closedBall c r)] (fun z => D (a + z • b)) :=
      (ae_restrict_mem measurableSet_closedBall).mono fun z hz => hdef z hz
    refine ⟨C, ?_, ?_, ?_⟩
    · intro z hz
      rw [heq _ (hs hz)]
      exact coe_sub_le C _
    · exact ((hD.onLine a b).aemeasurable.mono_measure
        (Measure.restrict_mono hs le_rfl)).congr hae.symm
    · have hmean := (hD.onLine a b).supermean c r hr hs
      have horder := EReal.sub_le_sub (le_refl (C : EReal))
        (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hmean)
      rw [heq _ hc]
      unfold diskMean
      change (C : EReal) - (D (a + c • b) : EReal) ≤
        (C : EReal) - (ENNReal.ofReal (Real.pi * r ^ 2)⁻¹ *
          ∫⁻ z in closedBall c r, deficit C Ψ (a + z • b) : ℝ≥0∞)
      rw [lintegral_congr_ae hae]
      exact horder

#print axioms plurisubharmonic_of_ball_representations

end V10.ERealPlurisubharmonic
