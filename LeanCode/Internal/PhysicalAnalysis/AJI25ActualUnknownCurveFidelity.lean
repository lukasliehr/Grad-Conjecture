import AJI24SameStoredUnknownInput
import AJL6ExactPolynomialPhysicalAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularSourceGraph
open Grad.AnnularRadialSmoothness Grad.AnnularSmoothSources Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

include allGrades

/-- This curve is the original homogeneous seven-input at its exact
polynomial grade, ready for the already checked physical kernel transport. -/
theorem sameUnknownCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      rawUnknownSevenOperator parameters radius
        (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field (radialClamp lower bounded.le radius),
          sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field (radialClamp lower bounded.le radius)) mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade + 1) : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive
            (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field) radius mode := by
  filter_upwards [homogeneousCoupledSevenInput_sameSections parameters lower length positive bounded lengthPositive field,
    ae_restrict_mem measurableSet_Icc] with radius stored inside
  intro mode
  have input := sameCoupledUnknownInput_coefficient parameters lower length positive bounded lengthPositive field allGrades grade
    (radialClamp lower bounded.le radius) mode
  have radiusSame : (radialClamp lower bounded.le radius).val = radius :=
    congrArg Subtype.val (radialClamp_eq lower bounded.le radius inside)
  rw [radiusSame] at input
  rw [input,
    sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades,
    sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  unfold lowRhoPhysicalCoefficient
  rw [stored mode, inv_smul_smul₀]
  · rw [Complex.ofReal_pow]
    rfl
  · exact Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne'

end Grad.AnnularSmoothCore
