import AKAK22SamePhysicalAxialDerivative
import AKAK9SameScalarPhysicalCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

private theorem scalarAxialCoordinateAlgebra (radius frequency : ℂ)
    (xi first second : ComplexEuclidean 1)
    (firstLaw : first = frequency • xi) (secondLaw : second = radius⁻¹ • xi) :
    radius⁻¹ • first = frequency • second := by
  rw [firstLaw,secondLaw,smul_comm]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)

/-- The literal original seven coordinates supply the axial relation,
including their different powers of radius. -/
theorem fullSeven_physicalXi_axialCoefficients :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      (radius : ℂ)⁻¹ • lowRhoPhysicalCoefficient parameters lower positive
        (Grad.AnnularCurrentEnergy.bulkMatrixUnit lower (0 : Fin 1) (2 : Fin 7)
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)) radius mode =
      (Complex.I * (mode.2 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive
        (Grad.AnnularCurrentEnergy.bulkMatrixUnit lower (0 : Fin 1) (3 : Fin 7)
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)) radius mode := by
  filter_upwards [fullStrongSevenInput_firstFour_physical parameters lower length positive bounded lengthPositive data field,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (2 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field),
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (3 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)]
      with radius actual first second
  intro mode
  rw [first mode,second mode]
  exact scalarAxialCoordinateAlgebra (radius : ℂ) (Complex.I * (mode.2 : ℂ))
    (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode)
    _ _ (actual mode 2) (actual mode 3)

variable
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

include allGrades smooth

/-- Genuine axial differentiation of the SAME original Xi produces its
literal slot two, with no additional PDE or regularity premise. -/
theorem fullSeven_physicalXi_axial (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1 (radius,polar,angle))
      ((seven.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial)) axial := by
  have law := samePhysical_scaledAxialDerivative (seven.bulkUnit (0 : Fin 1) 3) (seven.bulkUnit (0 : Fin 1) 2)
    bounded (fun location => (location : ℂ)⁻¹) (reciprocalRadius_smooth lower positive).continuousOn
    (fullSeven_physicalXi_axialCoefficients parameters lower length positive bounded lengthPositive data field)
    radius inside polar axial
  have nonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne'
  have same : (fun angle => (radius : ℂ) • (seven.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,polar,angle)) =
      fun angle => originalPhysicalComponentField parameters lower length positive bounded lengthPositive field 1 (radius,polar,angle) := by
    funext angle
    rw [fullSeven_physicalXiOverRadius parameters lower length positive bounded lengthPositive data field allGrades smooth seven radius inside (polar,angle),
      smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  have multiplied := law.const_smul (radius : ℂ)
  change HasDerivAt (fun angle => (radius : ℂ) • (seven.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,polar,angle))
    ((radius : ℂ) • ((radius : ℂ)⁻¹ • (seven.bulkUnit (0 : Fin 1) 2).fullField bounded (radius,polar,axial))) axial at multiplied
  rw [same] at multiplied
  simpa only [smul_smul,mul_inv_cancel₀ nonzero,one_smul] using multiplied

end Grad.ActualPolarEquations
