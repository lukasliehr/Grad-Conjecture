import AKV2GeneralOriginalUnknownInput

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
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)

/-- The actual original j, c and rV on the SAME inverse unknown packet,
represented with the original exponential phase and polynomial grade. -/
def generalConjugatedUnknownRowCurve (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) (grade + 1) 0 radius
    (generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius)

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
  CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

theorem generalConjugatedUnknownRowCurve_actual (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      generalConjugatedUnknownRowCurve parameters length compact lower positive bounded lengthPositive state field row grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade + 1) : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
                (homogeneousCoupledSevenInput parameters length lower lengthPositive positive
                  field)) radius mode) :=
  radialConjugatedAction_actual parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (homogeneousCoupledSevenInput parameters length lower lengthPositive positive
      field) (grade + 1)
    (generalConjugatedUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade)
    (generalConjugatedUnknownSevenCurve_actual parameters lower length positive bounded lengthPositive field allGrades grade)

end Grad.AnnularGeneralSourceRegularity
