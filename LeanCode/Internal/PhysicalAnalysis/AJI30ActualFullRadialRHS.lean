import AJI29ActualUnknownPhysicalRHS
import AJQ2ActualKnownSourceRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularSourceGraph Grad.AnnularRadialSmoothness Grad.AnnularSmoothSources
open Grad.AnnularStrongData Grad.AnnularStrongOrbit

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)
    (core : OriginalSmoothSourceCore parameters)

/-- Full original physical RHS: the homogeneous action on the SAME field
and the once-only known source, including independent f and positive Rg. -/
def actualOriginalFullRHS (radius : ℝ) (mode : ℤ × ℤ) :
    ComplexEuclidean 1 × ComplexEuclidean 1 :=
  actualOriginalUnknownRHS parameters length compact lower positive bounded lengthPositive state field radius mode +
    actualOriginalSourceRHS parameters length compact lower positive bounded lengthPositive state core radius mode

/-- The exact Hilbert RHS of the original (x,xi) radial system, using the
finite input loss two and the SAME closed-collar representative. -/
def originalRadialSystemRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  originalRadialSystemOperator parameters length compact lower state positive bounded grade radius
    (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius),
     sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius)) +
  originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

/-- Every grade of the continuous Hilbert formula has the literal full
physical Fourier coefficients, with all sources and signs retained. -/
theorem originalRadialSystemRHS_actual (grade : ℕ) :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      ((originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).1 mode,
       (originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        actualOriginalFullRHS parameters length compact lower positive bounded lengthPositive state field core radius mode := by
  filter_upwards [originalRadialSystemOperator_actual parameters length compact lower positive bounded lengthPositive state field allGrades grade,
    originalRadialSystemSource_actual parameters length compact lower positive bounded lengthPositive state core grade] with radius unknown source
  intro mode
  let input : PhysicalHilbertPair :=
    (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius),
     sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius))
  let output := originalRadialSystemOperator parameters length compact lower state positive bounded grade radius input
  let forcing := originalRadialSystemSource parameters length compact lower positive bounded lengthPositive state core grade radius
  change (output.1 mode, output.2 mode) + (forcing.1 mode, forcing.2 mode) = _
  rw [unknown mode, source mode, ← smul_add]
  rfl

end Grad.AnnularSmoothCore
