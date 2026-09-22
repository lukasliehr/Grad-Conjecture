import AKBT7SameScaledNativeMatrixCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

 theorem StartupWeightedRep.value {input output : ℕ} {sigma gamma ell : ℝ}
    {field : StartupL2 input} {raw : ℝ × Spatial → PhysicalValue input}
    (same : StartupWeightedRep sigma gamma ell field raw)
    (continuousRaw : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => raw (angle,point)))
    (mapping : OperatorValue input output) :
    StartupWeightedRep sigma gamma ell (originalValueKernel mapping field) (fun pair => mapping (raw pair)) := by
  filter_upwards [same,continuousRaw,startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) field]
    with point actual continuousAt represented
  intro cell
  change ∀ index : ℤ, originalValueKernel mapping field point index = mapping (field point index) at represented
  rw [represented cell,actual cell,startupAngularCoefficient_clm mapping _ continuousAt cell]
  exact (mapping.restrictScalars ℝ).map_smul _ _

 theorem StartupWeightedRep.add {dimension : ℕ} {sigma gamma ell : ℝ}
    {first second : StartupL2 dimension} {rawFirst rawSecond : ℝ × Spatial → PhysicalValue dimension}
    (firstSame : StartupWeightedRep sigma gamma ell first rawFirst)
    (secondSame : StartupWeightedRep sigma gamma ell second rawSecond)
    (firstContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => rawFirst (angle,point)))
    (secondContinuous : ∀ᵐ point ∂volume.restrict openUnitDisk, Continuous (fun angle => rawSecond (angle,point))) :
    StartupWeightedRep sigma gamma ell (first+second) (fun pair => rawFirst pair+rawSecond pair) := by
  filter_upwards [firstSame,secondSame,firstContinuous,secondContinuous,Lp.coeFn_add first second]
    with point firstAt secondAt firstRegular secondRegular value
  intro cell
  rw [value]
  change first point cell+second point cell = _
  rw [firstAt cell,secondAt cell,Grad.SourceCollarFullSource.angularCoefficient_add_general _ _ firstRegular secondRegular,smul_add]

end Grad.CartesianStartup
