import AKZ5ActualMatrixBulkAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.ActualPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularCrossOrbit Grad.AnnularStrongSolution
open Grad.AnnularStrongData Grad.AnnularKnownLow Grad.AnnularSmoothCore
open Grad.AnnularKernelL2 Grad.AnnularCurrentLow Grad.CircularHighRegularity Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph
open Grad.AnnularCurrentEnergy
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.WeightedTrace

theorem rawPhysicalSevenVector_scalarSlot (radius : ℝ) (mode : ℤ × ℤ) (x xi : ComplexEuclidean 1) :
    rawPhysicalSevenVector radius mode x xi 3 = (radius : ℂ)⁻¹ * xi 0 := by
  simp [rawPhysicalSevenVector,matrixUnit_apply,operatorBasis]

variable (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- Exact weighted storage of S/r for the SAME physical scalar section.
The known sources occupy slots4--6 and contribute nothing to this slot. -/
theorem fullStrongSevenInput_scalarOverRadius :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      bulkMatrixUnit lower (0 : Fin 1) (3 : Fin 7)
        (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) mode radius =
      (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) •
        ((radius : ℂ)⁻¹ • sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive solution 0
          (radialClamp lower bounded.le radius) mode) := by
  let free := homogeneousCoupledSevenInput parameters length lower lengthPositive positive solution
  let known := knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)
  have sums : ∀ mode : ℤ × ℤ, ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      (free mode + known mode) radius = free mode radius + known mode radius :=
    fun mode => Lp.coeFn_add (free mode) (known mode)
  filter_upwards [homogeneousCoupledSevenInput_sameSections parameters lower length positive bounded lengthPositive solution,
    knownLowSevenPacket_ae lower (strongKnownBulk parameters lower positive bounded.le data),
    ae_all_iff.mpr sums,
    bulkMatrixUnit_ae lower (0 : Fin 1) (3 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)]
    with radius actual knownLaw sumLaw extracted
  intro mode
  have sum : fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution mode radius =
      free mode radius + known mode radius := sumLaw mode
  rw [extracted mode,sum]
  change ((homogeneousCoupledSevenInput parameters length lower lengthPositive positive solution mode radius +
    knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data) mode radius) 3) • operatorBasis 0 = _
  rw [actual mode,knownLaw mode]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [operatorBasis,rawPhysicalSevenVector_scalarSlot]

theorem fullStrongScalarOverRadius_bound :
    ‖bulkMatrixUnit lower (0 : Fin 1) (3 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)‖ ≤
      (11 + 4 * length) * ‖solution‖ + 3 * ‖data‖ :=
  (bulkMatrixUnit_bound lower (0 : Fin 1) (3 : Fin 7) _).trans
    (fullStrongSevenInput_bound parameters length lower lengthPositive positive bounded.le data solution)

end Grad.ActualPhysicalField
