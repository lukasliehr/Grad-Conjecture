import AKBQ6SameGaugeFourierMeans

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.ActualScaledNativeCoefficients
open Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.ActualSmoothPhysicalField Grad.AnnularOriginalSmoothCore Grad.ActualPhysicalField
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.AnnularWeightedSmoothness
open Grad.AnnularCurrentEnergy Grad.AnnularRestriction Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularCoupledInverse Grad.AnnularFullGraph Grad.Constraints Grad.Constraints.Gauges Grad.CartesianStartup

/-- The actual original seven-packet supplies both scaled C0 gauge means; no gauge/PDE/H1 premise is added. -/
theorem originalPacket_scaledGaugeMeans {ell : ℝ} (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (admissible : Admissible length parameters.sigma0 parameters.gamma ell)
    (state : AnnularReconstructionState parameters length compact)
    (ledger : ActualLedger parameters admissible state.val.data.rho state.val.data.alpha state.val.data.delta
      state.val.data.parameter state.val.data.epsilon state.val.data.field)
    (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length positive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (originalSevenPacket parameters lower length positive bounded.le lengthPositive data candidate))
    (raw : ℝ×Spatial → PhysicalValue 3) (regular : StartupOrbitContinuous raw)
    (radius : ℝ) (radiusPositive : 0 < radius) (radiusInside : radius < 1) (radiusBounded : |radius| ≤ 1)
    (insidePhysical : ell*radius ∈ Icc lower 1)
    (same : ∀ polar axial, raw (axial,(Grad.Constraints.polarClosedPoint radius radiusBounded polar).val) =
      cartesianCovariantValue polar ((curves.covariant parameters length compact lower positive bounded state).fullField bounded
        (ell*radius,polar,axial))) (cell : ℤ) :
    angularCoefficient (fun polar => polarTangentialComponent polar (planarPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily ledger.val.gaugeDeviation) raw
        (axial,(Grad.Constraints.polarClosedPoint radius radiusBounded polar).val)) cell))) 0 = 0 ∧
    angularCoefficient (fun polar => toroidalPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily ledger.val.gaugeDeviation) raw
        (axial,(Grad.Constraints.polarClosedPoint radius radiusBounded polar).val)) cell)) 0 = 0 := by
  apply scaledRawGauge_cellMeans admissible state.val ledger raw regular radius radiusPositive radiusInside radiusBounded
    (fun angles => (curves.covariant parameters length compact lower positive bounded state).fullField bounded (ell*radius,angles))
    ((curves.covariant parameters length compact lower positive bounded state).fullField_continuous_angles bounded _ insidePhysical)
    same cell
  intro kind
  exact startupNative_originalPacket_physicalGaugeMean parameters length compact lower positive bounded lengthPositive
    state data candidate curves ⟨ell*radius,insidePhysical⟩ kind cell

end Grad.ActualScaledNativeCoefficients
