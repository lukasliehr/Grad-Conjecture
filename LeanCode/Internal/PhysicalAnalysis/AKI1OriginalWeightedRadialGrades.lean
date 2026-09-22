import AKH3ExactPhaseDiagonalCoefficient
import AKD3CopiedSourceConjugatedRadialCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set
open scoped ContDiff BigOperators Topology
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.PhaseAlgebra Grad.AnnularVariational
open Grad.SourceCollarCoefficients Grad.AnnularPhysicalFourier

abbrev AnnularCoefficient := ℝ → (ℤ × ℤ) → ComplexEuclidean 1

/-- Original phase and all inserted polynomial grades at the SAME radius.
The smoothness is on the entire closed collar, not just its interior. -/
def PhaseWeightedRadialSmooth (parameters : PhaseParameters) (lower : ℝ)
    (coefficient : AnnularCoefficient) : Prop :=
  ∃ curve : ℕ → ℝ → CellL2 1,
    (∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1)) ∧
    ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode,
      curve grade radius mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • coefficient radius mode)

theorem phaseWeightedRadialSmooth_zero (parameters : PhaseParameters) (lower : ℝ) :
    PhaseWeightedRadialSmooth parameters lower 0 := by
  refine ⟨0, fun _ => contDiffOn_const, ?_⟩
  intro grade radius _ mode
  simp

theorem PhaseWeightedRadialSmooth.add {parameters : PhaseParameters} {lower : ℝ}
    {first second : AnnularCoefficient} (firstSmooth : PhaseWeightedRadialSmooth parameters lower first)
    (secondSmooth : PhaseWeightedRadialSmooth parameters lower second) :
    PhaseWeightedRadialSmooth parameters lower (first + second) := by
  obtain ⟨firstCurve, firstRegular, firstSame⟩ := firstSmooth
  obtain ⟨secondCurve, secondRegular, secondSame⟩ := secondSmooth
  refine ⟨firstCurve + secondCurve, fun grade => (firstRegular grade).add (secondRegular grade), ?_⟩
  intro grade radius inside mode
  change firstCurve grade radius mode + secondCurve grade radius mode = _
  rw [firstSame grade radius inside mode, secondSame grade radius inside mode]
  simp only [Pi.add_apply, smul_add]

theorem PhaseWeightedRadialSmooth.smul {parameters : PhaseParameters} {lower : ℝ}
    {coefficient : AnnularCoefficient} (smooth : PhaseWeightedRadialSmooth parameters lower coefficient)
    (scalar : ℂ) : PhaseWeightedRadialSmooth parameters lower (scalar • coefficient) := by
  obtain ⟨curve, regular, same⟩ := smooth
  refine ⟨scalar • curve, fun grade => (regular grade).const_smul scalar, ?_⟩
  intro grade radius inside mode
  change scalar • curve grade radius mode = _
  rw [same grade radius inside mode]
  simp only [Pi.smul_apply]
  rw [smul_comm scalar, smul_comm scalar]

/-- A genuine linear coefficient carrier; no equation or residual variable
occurs in its definition. -/
def phaseWeightedCoefficientSpace (parameters : PhaseParameters) (lower : ℝ) :
    Submodule ℂ AnnularCoefficient where
  carrier := PhaseWeightedRadialSmooth parameters lower
  zero_mem' := phaseWeightedRadialSmooth_zero parameters lower
  add_mem' := fun first second => first.add second
  smul_mem' := fun scalar _ smooth => smooth.smul scalar

theorem phaseWeightedCurve_grade {parameters : PhaseParameters} {lower : ℝ}
    (coefficient : AnnularCoefficient) (curve : ℕ → ℝ → CellL2 1)
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode,
      curve grade radius mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((Real.exp (radialPhase parameters radius mode.2) : ℂ) • coefficient radius mode))
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curve grade radius mode = ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode := by
  rw [same grade radius inside mode, same 0 radius inside mode]
  simp only [pow_zero, Complex.ofReal_one, one_smul]

/-- Every original radial derivative of W h has uniformly summable full
Fourier grades. This proves finiteness; it is not a core-membership premise. -/
theorem PhaseWeightedRadialSmooth.radialGrades {parameters : PhaseParameters} {lower : ℝ}
    {coefficient : AnnularCoefficient} (smooth : PhaseWeightedRadialSmooth parameters lower coefficient)
    (bounded : lower < 1) :
    ∃ sections : ℕ → (ℤ × ℤ) → C(Icc lower (1 : ℝ), ComplexEuclidean 1),
      (∀ order mode radius,
        sections order mode radius = iteratedDerivWithin order
          (fun point => (Real.exp (radialPhase parameters point mode.2) : ℂ) • coefficient point mode)
          (Icc lower 1) radius.val) ∧
      ∀ order grade, Summable (fun mode : ℤ × ℤ =>
        annularFrequency mode.1 mode.2 ^ grade * ‖sections order mode‖) := by
  obtain ⟨curve, regular, same⟩ := smooth
  refine ⟨fun order mode => hilbertRadialJetSection lower bounded curve regular order 0 mode, ?_, ?_⟩
  · intro order mode radius
    let evaluate := lp.evalCLM ℝ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode
    change evaluate (iteratedDerivWithin order (curve 0) (Icc lower 1) radius.val) = _
    rw [← radialJet_map lower bounded (curve 0) (regular 0) evaluate order radius.val radius.property]
    apply iteratedDerivWithin_congr _ radius.property
    intro point inside
    change curve 0 point mode = _
    simpa only [pow_zero, Complex.ofReal_one, one_smul] using same 0 point inside mode
  · exact fun order grade => hilbertRadialJetSection_weighted_summable lower bounded curve regular
      (phaseWeightedCurve_grade coefficient curve same) order grade

end Grad.AnnularOriginalSmoothCore
