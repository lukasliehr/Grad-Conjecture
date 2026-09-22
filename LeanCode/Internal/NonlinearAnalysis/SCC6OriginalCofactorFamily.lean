import SCC5OriginalInverseRealization

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger

def originalFullFrameFamily (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fun grade => constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame grade +
    originalFrameFamily parameters L epsilon field grade

def originalFullFrameProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  ⟨fixedFamilyConstant referenceFrame, originalFrameConstant parameters L⟩

theorem originalFullFrameFamily_estimate (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (epsilonSmall : |epsilon| ≤ 1) :
    FamilyEstimate parameters field rho epsilon 4 (originalFullFrameProfile parameters L)
      (originalFullFrameFamily parameters L epsilon field)
      (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame) where
  actualCoherent := (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame).add
    (originalFrameFamily_coherent parameters L epsilon field)
  referenceCoherent := constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame
  fixedNonnegative := fixedFamilyConstant_nonnegative referenceFrame
  deviationNonnegative := originalFrameConstant_nonnegative parameters L
  referenceBound := constantFamily_norm_le (unitDiskAdmissible parameters) referenceFrame
  deviationBound grade := by
    change ‖(_ + originalFrameFamily parameters L epsilon field grade) - _‖ ≤ _
    rw [add_sub_cancel_left]
    exact originalFrameFamily_bound parameters L rho epsilon field epsilonSmall grade

theorem originalFullFrameFamily_matrix (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalFullFrameFamily parameters L epsilon field) grade angle point =
      originalPhysicalFrameMatrix parameters L epsilon field angle point := by
  unfold familyMatrix originalFullFrameFamily
  rw [family_physicalValue_add (unitDiskAdmissible parameters) _ _
    (constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame)
    (originalFrameFamily_coherent parameters L epsilon field),
    constantFamily_physicalValue (unitDiskAdmissible parameters), originalFrameFamily_physicalValue]
  rfl

def originalCofactorFamily (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fluxFamily (unitDiskAdmissible parameters) (originalFullFrameFamily parameters L epsilon field)
    (originalInverseFamily parameters L epsilon field)

def originalCofactorReference (parameters : PhaseParameters) :
    CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3 :=
  fluxFamily (unitDiskAdmissible parameters)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame)
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame)

def originalCofactorProfile (parameters : PhaseParameters) (L : ℝ) : EstimateProfile :=
  fluxProfile (originalFullFrameProfile parameters L) (originalInverseProfile parameters L)

/-- One high original B_(q+4), on the single B6 neighborhood. All products,
inverse words and full cell displacements come from accepted GC15–17. -/
theorem originalCofactorFamily_estimate (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L) :
    FamilyEstimate parameters field rho epsilon 4 (originalCofactorProfile parameters L)
      (originalCofactorFamily parameters L epsilon field) (originalCofactorReference parameters) := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  exact fluxFamily_estimate (unitDiskAdmissible parameters) margin.2.1
    (originalFullFrameFamily_estimate parameters L rho epsilon field margin.1)
    (originalInverseFamily_estimate parameters L rho epsilon field low)

theorem originalCofactorReference_matrix (parameters : PhaseParameters)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalCofactorReference parameters) grade angle point = -1 :=
  fluxFamily_circle (unitDiskAdmissible parameters) grade angle point

theorem originalCofactorFamily_matrix (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalCofactorFamily parameters L epsilon field) grade angle point =
      (originalPhysicalFrameMatrix parameters L epsilon field angle point).det •
        (familyMatrix (originalInverseFamily parameters L epsilon field) grade angle point *
          (familyMatrix (originalInverseFamily parameters L epsilon field) grade angle point).transpose) := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  rw [originalCofactorFamily, fluxFamily_matrix (unitDiskAdmissible parameters) _ _
    (originalFullFrameFamily_estimate parameters L rho epsilon field margin.1).actualCoherent
    (originalInverseFamily_coherent parameters L epsilon field margin.2.2), originalFullFrameFamily_matrix]

end Grad.SourceCollarCoefficients
