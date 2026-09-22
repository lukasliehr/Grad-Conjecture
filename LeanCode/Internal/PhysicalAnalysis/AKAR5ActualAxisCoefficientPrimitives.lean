import AKAR3AngularCoefficientKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Envelope

/-- Cartesian cofactor covector before the fixed polar radial projection. -/
def originalCofactorCovectorFamily (parameters : PhaseParameters) (length epsilon : ℝ) (base : ACore parameters 3) :=
  composeFamily (unitDiskAdmissible parameters) (originalCofactorFamily parameters length epsilon base)
    (transposeFamily (unitDiskAdmissible parameters) (originalFullFrameFamily parameters length epsilon base))

def originalCofactorCovectorProfile (parameters : PhaseParameters) (length : ℝ) :=
  (originalCofactorProfile parameters length).comp 4 (transposeProfile 4 3 3 (originalFullFrameProfile parameters length))

theorem originalCofactorCovectorFamily_estimate (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length) :
    FamilyEstimate parameters base rho epsilon 4 (originalCofactorCovectorProfile parameters length)
      (originalCofactorCovectorFamily parameters length epsilon base)
      (composeFamily (unitDiskAdmissible parameters) (originalCofactorReference parameters)
        (transposeFamily (unitDiskAdmissible parameters)
          (constantFamily 1 parameters.sigma0 parameters.gamma 1 Grad.GaugeCoefficients.Physical.Frame.referenceFrame))) := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon base small
  exact FamilyEstimate.comp (unitDiskAdmissible parameters) margin.2.1
    (originalCofactorFamily_estimate parameters length rho epsilon base small)
    (transposeFamily_estimate (unitDiskAdmissible parameters) margin.2.1
      (originalFullFrameFamily_estimate parameters length rho epsilon base margin.1))

theorem familyEstimate_bounded_grade {input output : ℕ} (parameters : PhaseParameters)
    (rho epsilon : ℝ) (base : ACore parameters 3) (profile : EstimateProfile)
    (actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (estimate : FamilyEstimate parameters base rho epsilon 4 profile actual reference)
    (small : physicalBudget parameters base rho epsilon 8 ≤ 1) (grade : ℕ) (bounded : grade ≤ 4) :
    ‖actual grade‖ ≤ profile.fixed grade + profile.deviation grade := by
  have lower := (physicalBudget_monotone parameters base rho epsilon (show 4+grade ≤ 8 by omega)).trans small
  have triangle : ‖actual grade‖ ≤ ‖actual grade-reference grade‖ + ‖reference grade‖ := by
    simpa only [sub_add_cancel] using norm_add_le (actual grade-reference grade) (reference grade)
  have combined := triangle.trans (add_le_add (estimate.deviationBound grade) (estimate.referenceBound grade))
  nlinarith [mul_nonneg (estimate.deviationNonnegative grade) (sub_nonneg.mpr lower)]

theorem originalAxis_primitive_margin (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length) :
    physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length ∧
      physicalBudget parameters base rho epsilon 8 ≤ 1 :=
  ⟨(physicalBudget_monotone parameters base rho epsilon (by omega : 6 ≤ 8)).trans small,
    small.trans (min_le_left _ _)⟩

end Grad.OriginalKernelRetainedDecay
