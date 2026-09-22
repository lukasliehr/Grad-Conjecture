import AJI25ActualUnknownCurveFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularSourceGraph Grad.AnnularRadialSmoothness Grad.AnnularSmoothSources
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity

variable (parameters : PhaseParameters) (lower length compact : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)

def sameUnknownSevenCurve (grade : ℕ) (radius : ℝ) : CellL2 7 :=
  rawUnknownSevenOperator parameters radius
    (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field (radialClamp lower bounded.le radius),
      sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field (radialClamp lower bounded.le radius))

def sameUnknownPhysicalRowCurve (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radialPolynomialAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) (grade + 1) radius
    (sameUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade radius)

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

/-- Genuine full physical j/c/rV kernel action on the same unknown fields,
with no finite-mode replacement and with the original rho/phase decode. -/
theorem sameUnknownPhysicalRowCurve_actual (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      sameUnknownPhysicalRowCurve parameters lower length compact positive bounded lengthPositive state field row grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade + 1) : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
              (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)) radius mode :=
  radialPolynomialAction_actual parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)
    (grade + 1) (sameUnknownSevenCurve parameters lower length positive bounded lengthPositive field grade)
    (sameUnknownCurve_actual parameters lower length positive bounded lengthPositive field allGrades grade)

end Grad.AnnularSmoothCore
