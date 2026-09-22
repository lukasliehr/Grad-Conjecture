import AEE2ActualScalarRadialCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The actual normalized reference coefficient, extended continuously only
for the L2 multiplier construction and unchanged on the physical annulus. -/
def lowNormalizedReferenceCurve (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) (row column : Fin 2) : C(ℝ, ℝ) where
  toFun radius := lowNormalizedReferenceCoefficient parameters length (max lower radius) mode row column
  continuous_toFun := continuous_iff_continuousAt.mpr (fun radius => by
    have floorPositive := positive.trans_le (le_max_left lower radius)
    have numerator := lowReferenceEntry_continuousAt parameters length (max lower radius) mode floorPositive row column
    have denominator := (lowMu_hasDerivAt length (max lower radius) mode.val.2 floorPositive).continuousAt
    exact (numerator.div denominator (lowMu_pos length (max lower radius) mode.val.2 floorPositive).ne').comp
      (continuous_const.max continuous_id).continuousAt)

theorem lowNormalizedReferenceCurve_actual (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (mode : LowAnnularMode) (row column : Fin 2) (radius : ℝ)
    (inside : lower ≤ radius) :
    lowNormalizedReferenceCurve parameters length lower positive mode row column radius =
      lowReferenceMatrix parameters length radius mode row column / lowMu length radius mode.val.2 := by
  change lowNormalizedReferenceCoefficient parameters length (max lower radius) mode row column = _
  rw [max_eq_right inside]
  rfl

theorem lowNormalizedReferenceCurve_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (mode : LowAnnularMode) (row column : Fin 2)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |lowNormalizedReferenceCurve parameters length lower positive mode row column radius| ≤
      lowReferenceCoefficientConstant parameters length := by
  rw [lowNormalizedReferenceCurve_actual parameters length lower positive mode row column radius inside.1]
  exact lowNormalizedReferenceCoefficient_bound parameters length radius lengthPositive
    (positive.trans_le inside.1) inside.2 mode row column

/-- Uniform diagonal scalar matrix multiplication in rho-stored radial L2,
using the accepted actual measurable matrix multiplier and lp lift. -/
def lowRadialDiagonal (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (column : LowAnnularIndex → Fin 2) :
    LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  complexLpTwoMap
    (fun index => scalarRadialMap lower
      (lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 (column index))
      (lowReferenceCoefficientConstant parameters length)
      (lowNormalizedReferenceCurve_bound parameters length lower lengthPositive positive index.2 index.1 (column index)))
    (lowReferenceCoefficientConstant parameters length)
    (lowReferenceCoefficientConstant_pos parameters length lengthPositive).le
    (fun _ field => scalarRadialMap_bound _ _ _ _ field)

theorem lowRadialDiagonal_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (column : LowAnnularIndex → Fin 2)
    (field : LowEnergyBulk lower) :
    ‖lowRadialDiagonal parameters length lower lengthPositive positive column field‖ ≤
      lowReferenceCoefficientConstant parameters length * ‖field‖ :=
  complexLpTwoMap_bound _ _ _ _ field

theorem lowRadialDiagonal_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (column : LowAnnularIndex → Fin 2)
    (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowRadialDiagonal parameters length lower lengthPositive positive column field index radius =
        (lowReferenceMatrix parameters length radius index.2 index.1 (column index) /
          lowMu length radius index.2.val.2) • field index radius := by
  have actual := scalarRadialMap_ae lower
    (lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 (column index))
    (lowReferenceCoefficientConstant parameters length)
    (lowNormalizedReferenceCurve_bound parameters length lower lengthPositive positive index.2 index.1 (column index))
    (field index)
  filter_upwards [actual, ae_restrict_mem measurableSet_Icc] with radius actual inside
  rw [lowNormalizedReferenceCurve_actual parameters length lower positive index.2 index.1 (column index) radius inside.1] at actual
  exact actual

end Grad.AnnularLowCompletion
