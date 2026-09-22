import AKDI6OriginalSeedZeroSource
import AKU85ActualCurrentSpecialization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
namespace Grad.OriginalZeroSeed
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.SmoothingFamily
open Grad.PhysicalCoordinates Grad.Q24Realization Grad.RealFixedRanges Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation

variable {parameters : PhaseParameters}

theorem seedMatrixCore_zero_eccentricity (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (zeroEccentricity : seed 0 = 0) (field : ACore parameters 2) :
    Gauges.seedMatrixCore parameters seed inside field = field := by
  apply coreValue_ext
  intro point axial
  rw [coreValue_seedMatrix,zeroEccentricity,seedOperator_double_angle]
  norm_num [seedIsotropic,seedAnisotropic]

theorem tameSeedField_zero_eccentricity (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (zeroEccentricity : seed 0 = 0) :
    tameSeedField parameters seed inside = planarReferenceCore parameters := by
  rw [tameSeedField,tameSeedPlanarField,seedMatrixCore_zero_eccentricity seed inside zeroEccentricity]
  rfl

theorem actualFiniteCurrentField_seed_zero (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (epsilon : ℝ) :
    actualFiniteCurrentField parameters reference insideR seed insideS (epsilon,0) =
      tameSeedField parameters seed insideS - planarReferenceCore parameters := by
  unfold actualFiniteCurrentField actualFiniteCurrentChart
  change normalizedChartDisplacement parameters seed insideS
    (physicalFixedReferenceTransfer parameters reference insideR seed insideS
      (smoothingChartCore parameters (0 : StateCore parameters))) = _
  rw [smoothingChartCore_zero]
  have transfer : physicalFixedReferenceTransfer parameters reference insideR seed insideS
      (0 : ChartState parameters) = 0 := by
    change (0,toPhysicalCore parameters (Gauges.seedTransfer parameters reference insideR seed insideS 0),0) = (0,0,0)
    simp only [map_zero]
  rw [transfer,normalizedChartDisplacement,normalizedChart_zero]

theorem actualFiniteCurrentField_zero_eccentricity (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (zeroEccentricity : seed 0 = 0) (epsilon : ℝ) :
    actualFiniteCurrentField parameters reference insideR seed insideS (epsilon,0) = 0 := by
  rw [actualFiniteCurrentField_seed_zero,tameSeedField_zero_eccentricity seed insideS zeroEccentricity,sub_self]

theorem actualFiniteCurrentBudget_zero (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (zeroEccentricity : seed 0 = 0) (grade : ℕ) :
    physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS (0,0)) (seed 0) 0 grade = 0 := by
  rw [actualFiniteCurrentField_zero_eccentricity reference insideR seed insideS zeroEccentricity]
  simp only [physicalBudget,zeroEccentricity,originalGradeNorm_zero,abs_zero,add_zero]

end Grad.OriginalZeroSeed
