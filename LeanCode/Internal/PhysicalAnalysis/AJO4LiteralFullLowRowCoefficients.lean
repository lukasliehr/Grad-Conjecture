import AJO3ActualPhysicalLowDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowClassical
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularRegularity
open Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.PhaseAlgebra

/-- Literal common diagonal and three full original physical rows. -/
def lowFullRowRHS (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (value : LowEnergyBulk lower) (first cell angular : DivisionRow 1 lower) : LowEnergyBulk lower :=
  lowCommonDiagonal parameters length lower lengthPositive positive value +
    lowFirstOutput parameters lower length first + lowCellOutput lower length positive cell +
    lowAngularOutput lower length positive angular

theorem lowFullRowRHS_ae (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (value : LowEnergyBulk lower) (first cell angular : DivisionRow 1 lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowFullRowRHS parameters lower length positive lengthPositive value first cell angular index radius =
        ((annularPhaseSlope parameters index.2.val.2 radius +
          if index.1 = 0 then lowMuLogSlope length radius index.2.val.2 else -1 / radius) / lowMu length radius index.2.val.2) • value index radius +
        (if index.1 = 0 then lowAmplitude length parameters.gamma index.2 • first index.2.val radius else 0) +
        (if index.1 = 1 then (-Complex.I) • (((index.2.val.2 : ℝ) / length / lowMu length radius index.2.val.2) • cell index.2.val radius) else 0) +
        (if index.1 = 1 then (-Complex.I) • (((index.2.val.1 : ℝ) * radius⁻¹ / lowMu length radius index.2.val.2) • angular index.2.val radius) else 0) := by
  let diagonal := lowCommonDiagonal parameters length lower lengthPositive positive value index
  let firstRow := lowFirstOutput parameters lower length first index
  let cellRow := lowCellOutput lower length positive cell index
  let angularRow := lowAngularOutput lower length positive angular index
  filter_upwards [lowCommonDiagonal_ae parameters length lower lengthPositive positive value index,
    lowFirstOutput_ae parameters lower length first index,
    lowCellOutput_ae lower length positive cell index,
    lowAngularOutput_ae lower length positive angular index,
    Lp.coeFn_add diagonal firstRow, Lp.coeFn_add (diagonal + firstRow) cellRow,
    Lp.coeFn_add ((diagonal + firstRow) + cellRow) angularRow]
    with radius diagonalLaw firstLaw cellLaw angularLaw firstAdd secondAdd thirdAdd
  change (((diagonal + firstRow) + cellRow) + angularRow) radius = _
  rw [thirdAdd]
  simp only [Pi.add_apply]
  rw [secondAdd]
  simp only [Pi.add_apply]
  rw [firstAdd]
  simp only [Pi.add_apply]
  rw [diagonalLaw, firstLaw, cellLaw, angularLaw]

/-- Actual unnormalized weak derivative recovered from the stored row,
using the original mu and r^-7/4 storage rather than a replacement graph. -/
theorem lowEnergyDerivative_fullRows_ae (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : lowEnergyGraph lower length positive) (first cell angular : DivisionRow 1 lower)
    (equation : field.val 1 = lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular)
    (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowEnergyDerivative lower length positive index field.val radius =
        lowMu length radius index.2.val.2 • (lowStorageInverse lower positive radius •
          lowFullRowRHS parameters lower length positive lengthPositive (field.val 0) first cell angular index radius) := by
  have outer := collarScalar_ae 1 lower (lowMuCurve lower length positive index.2.val.2)
    (collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index))
  have inner := collarScalar_ae 1 lower (lowStorageInverse lower positive) (field.val 1 index)
  filter_upwards [outer, inner, ae_restrict_mem measurableSet_Icc] with radius outer inner inside
  change collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)
    (collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index)) radius = _
  rw [outer, inner, equation]
  change lowMu length (max lower radius) index.2.val.2 • _ = _
  rw [max_eq_right inside.1]

end Grad.AnnularLowClassical
