import AKV3GeneralOriginalUnknownRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularGeneralSourceRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2 Grad.AnnularWeightedSystem

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

/-- Exact common-phase relation to the accepted physical unknown rows.
Both sides act on the SAME field with the SAME original kernel. -/
theorem generalConjugatedUnknownRowCurve_physical (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      generalConjugatedUnknownRowCurve parameters length compact lower positive bounded lengthPositive state field row grade radius mode =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          sameUnknownPhysicalRowCurve parameters lower length compact positive
            bounded lengthPositive state
            (field) row grade radius mode := by
  filter_upwards [generalConjugatedUnknownRowCurve_actual parameters length compact lower positive bounded lengthPositive state field allGrades row grade,
    sameUnknownPhysicalRowCurve_actual parameters lower length compact positive
      bounded lengthPositive state
      (field)
      (allGrades) row grade] with radius weighted physical
  intro mode
  rw [weighted mode, physical mode]
  exact smul_comm _ _ _

/-- The actual conjugated homogeneous operator is exactly the original
physical radial system after inserting exp(Phi), at every Fourier grade. -/
theorem generalConjugatedRadialSystemOperator_physical (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      hilbertPairCoefficient mode
        (conjugatedRadialSystemOperator parameters length compact lower state positive
          bounded grade radius
          (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius)) =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          hilbertPairCoefficient mode
            (originalRadialSystemOperator parameters length compact lower state positive
              bounded grade radius
              (originalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius)) := by
  filter_upwards [generalConjugatedUnknownRowCurve_physical parameters length compact lower positive bounded lengthPositive state field allGrades 0 grade,
    generalConjugatedUnknownRowCurve_physical parameters length compact lower positive bounded lengthPositive state field allGrades 1 grade,
    generalConjugatedUnknownRowCurve_physical parameters length compact lower positive bounded lengthPositive state field allGrades 2 grade,
    ae_restrict_mem measurableSet_Icc] with radius sameJ sameC sameV inside
  intro mode
  rw [conjugatedRadialSystemOperator_coefficient]
  have physicalFormula := originalRadialSystemOperator_coefficient parameters lower length compact positive
    bounded state grade radius
    (originalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius) mode
  dsimp only at physicalFormula
  change _ = (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
    ((originalRadialSystemOperator parameters length compact lower state positive
      bounded grade radius
      (originalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius)).1 mode,
     (originalRadialSystemOperator parameters length compact lower state positive
      bounded grade radius
      (originalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius)).2 mode)
  rw [physicalFormula]
  change conjugatedUnknownPointRHS length radius mode
      ((conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius).1 mode)
      (generalConjugatedUnknownRowCurve parameters length compact lower positive bounded lengthPositive state field 0 grade radius mode)
      (generalConjugatedUnknownRowCurve parameters length compact lower positive bounded lengthPositive state field 1 grade radius mode)
      (generalConjugatedUnknownRowCurve parameters length compact lower positive bounded lengthPositive state field 2 grade radius mode) = _
  rw [sameJ mode, sameC mode, sameV mode]
  have sameX := congrArg Prod.fst (conjugatedOriginalPairCurve_physical parameters lower length positive bounded lengthPositive field allGrades (grade+2) radius inside mode)
  change (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius).1 mode =
      (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        (originalPairCurve parameters lower length positive bounded lengthPositive field (grade + 2) radius).1 mode at sameX
  rw [sameX, conjugatedUnknownPointRHS_smul]
  rfl

end Grad.AnnularGeneralSourceRegularity
