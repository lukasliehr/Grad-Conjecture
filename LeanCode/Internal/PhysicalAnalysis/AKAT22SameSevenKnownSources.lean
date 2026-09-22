import AKAT21SameLiteralPrimitiveSources

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianEquations
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarBulk Grad.SourceCollarRestriction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarFlux Grad.BoundaryTrace Grad.SourceCollar
open Grad.AnnularGeneralSourceRegularity Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularStrongOrbit Grad.AnnularSourceGraph Grad.AnnularForwardDatum Grad.AnnularRestriction
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.BoundaryLift Grad.ActualOriginalThirdSource
open Grad.AnnularSmoothCore Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCoupledInverse
open Grad.AnnularKnownLow Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators Grad.ActualPolarEquations

def knownSevenSlot : Fin 3 → Fin 7 := ![4,5,6]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- The same full packet contains exactly the prescribed F0,RF0,F2 once. -/
theorem fullStrongSevenInput_known_physical :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ, ∀ index : Fin 3,
      matrixUnit (0 : Fin 1) (knownSevenSlot index)
        (lowRhoPhysicalCoefficient parameters lower positive
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) radius mode) =
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive bounded.le data (index.castLE (by omega : 3 ≤ 4))) radius mode := by
  let unknown := homogeneousCoupledSevenInput parameters length lower lengthPositive positive solution
  let known := knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)
  filter_upwards [lowRhoPhysicalCoefficient_add_ae parameters lower positive unknown known,
    homogeneousCoupledSevenInput_sameSections parameters lower length positive bounded lengthPositive solution,
    knownPacket_physical_ae parameters lower positive (strongKnownBulk parameters lower positive bounded.le data)]
    with radius added original sources
  intro mode index
  have unknownSame : lowRhoPhysicalCoefficient parameters lower positive unknown radius mode =
      rawPhysicalSevenVector radius mode
        (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive solution 0 (radialClamp lower bounded.le radius) mode)
        (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive solution 0 (radialClamp lower bounded.le radius) mode) := by
    unfold lowRhoPhysicalCoefficient
    rw [original mode,inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne')]
  change matrixUnit (0 : Fin 1) (knownSevenSlot index)
    (lowRhoPhysicalCoefficient parameters lower positive (unknown+known) radius mode) = _
  rw [added mode,map_add,unknownSame,sources mode]
  apply PiLp.ext
  intro component
  fin_cases component
  fin_cases index <;> simp [knownSevenSlot,rawPhysicalSevenVector,rawOriginalKnownSevenVector,matrixUnit_apply,operatorBasis]

theorem sameSevenKnown_fullField
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (index : Fin 3)
    (source : SmoothLowPhysicalRow parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le data (index.castLE (by omega : 3 ≤ 4))))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (seven.bulkUnit (0 : Fin 1) (knownSevenSlot index)).fullField bounded (radius,angles) =
      source.fullField bounded (radius,angles) := by
  apply samePhysical_fullField_eq _ source bounded ?_ radius inside angles
  filter_upwards [fullStrongSevenInput_known_physical parameters lower length positive bounded lengthPositive data solution,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (knownSevenSlot index)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)] with current given projected
  intro mode
  rw [projected mode]
  exact given mode index

end Grad.ActualCartesianEquations
