import GC17Assembly

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

def physicalLedgerData {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3) :
    LedgerData L parameters.sigma0 parameters.gamma ell :=
  assembleData admissible (fullFrameFamily parameters L ell epsilon field)
    (actualFrameInverse parameters admissible epsilon field)
    (seedMatrixFamily admissible rho alpha delta parameter)
    (actualSeedInverse admissible rho alpha delta parameter)
    (fun grade => seedDerivativeCoefficient admissible grade rho alpha delta parameter)
    (actualRotatedFrame parameters admissible epsilon field)

/-- All nine output families are constructed from the original physical state
and actual harmonic seed. Only the two already derived low inversion margins
enter these correspondence proofs. -/
def physicalLedger {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (frameBase : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (seedBase : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4) :
    ActualLedger parameters admissible rho alpha delta parameter epsilon field := by
  have frameCoherent : FamilyCoherent (fullFrameFamily parameters L ell epsilon field) :=
    (constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame).add
      (actualFrameFamily_coherent parameters admissible epsilon field)
  have inverseCoherent := actualFrameInverse_coherent parameters admissible epsilon field frameBase
  have seedCoherent : FamilyCoherent (seedMatrixFamily admissible rho alpha delta parameter) :=
    (identityFamily_coherent L parameters.sigma0 parameters.gamma ell 2).add
      (seedDeviationFamily_coherent admissible rho alpha delta parameter)
  have seedInverseCoherent := actualSeedInverse_coherent admissible rho alpha delta parameter seedBase
  have derivativeCoherent := seedDerivativeFamily_coherent admissible rho alpha delta parameter
  have rotatedCoherent := actualRotatedFrame_coherent parameters admissible epsilon field
  refine ⟨physicalLedgerData parameters admissible rho alpha delta parameter epsilon field,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact assembleData_coherent admissible _ _ _ _ _ _ frameCoherent inverseCoherent seedCoherent
      seedInverseCoherent derivativeCoherent rotatedCoherent
  · intro grade angle point
    exact actualFrameInverse_matrix_identity parameters admissible epsilon field frameBase grade angle point
  · intro grade angle point
    exact actualSeedInverse_matrix_identity admissible rho alpha delta parameter seedBase grade angle point
  · intro grade angle point
    exact assembleData_transpose_matrix admissible _ _ _ _ _ _ inverseCoherent grade angle point
  · intro grade angle point
    have formula := assembleData_gauge_matrix admissible
      (fullFrameFamily parameters L ell epsilon field) (actualFrameInverse parameters admissible epsilon field)
      (seedMatrixFamily admissible rho alpha delta parameter) (actualSeedInverse admissible rho alpha delta parameter)
      (fun q => seedDerivativeCoefficient admissible q rho alpha delta parameter)
      (actualRotatedFrame parameters admissible epsilon field) seedCoherent derivativeCoherent inverseCoherent grade angle point
    rw [seedMatrixFamily_matrix admissible, seedDerivativeFamily_matrix admissible] at formula
    exact formula
  · intro grade angle point
    have formula := assembleData_flux_matrix admissible
      (fullFrameFamily parameters L ell epsilon field) (actualFrameInverse parameters admissible epsilon field)
      (seedMatrixFamily admissible rho alpha delta parameter) (actualSeedInverse admissible rho alpha delta parameter)
      (fun q => seedDerivativeCoefficient admissible q rho alpha delta parameter)
      (actualRotatedFrame parameters admissible epsilon field) frameCoherent inverseCoherent grade angle point
    rw [fullFrameFamily_matrix parameters admissible] at formula
    exact formula
  · intro grade angle point
    exact assembleData_trace_matrix admissible _ _ _ _ _ _ seedInverseCoherent inverseCoherent grade angle point
  · intro grade angle point
    exact actualRotatedFrame_physicalValue parameters admissible epsilon field grade angle point
  · intro grade angle point
    have formula := rotatedProduct_deviation_matrix admissible planarFrameColumns
      (actualRotatedFrame parameters admissible epsilon field) (actualFrameInverse parameters admissible epsilon field)
      rotatedCoherent inverseCoherent grade angle point
    change operatorMatrix (coefficientPhysicalValue
      ((physicalLedgerData parameters admissible rho alpha delta parameter epsilon field).rotatedPlanarProduct grade)
      angle point) = _ at formula
    rw [show familyMatrix (actualRotatedFrame parameters admissible epsilon field) grade angle point =
      rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point from
        actualRotatedFrame_physicalValue parameters admissible epsilon field grade angle point] at formula
    exact formula
  · intro grade angle point
    have formula := rotatedProduct_deviation_matrix admissible thirdFrameColumn
      (actualRotatedFrame parameters admissible epsilon field) (actualFrameInverse parameters admissible epsilon field)
      rotatedCoherent inverseCoherent grade angle point
    change operatorMatrix (coefficientPhysicalValue
      ((physicalLedgerData parameters admissible rho alpha delta parameter epsilon field).rotatedThirdProduct grade)
      angle point) = _ at formula
    rw [show familyMatrix (actualRotatedFrame parameters admissible epsilon field) grade angle point =
      rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point from
        actualRotatedFrame_physicalValue parameters admissible epsilon field grade angle point] at formula
    exact formula

end Grad.GaugeCoefficients.Physical.Ledger
