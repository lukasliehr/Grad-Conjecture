import AEI8ActualNormalizedLowOutputMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

def lowSevenInputSymbol (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) (first second : ComplexEuclidean 1) : ComplexEuclidean 7 :=
  (second 0) • operatorBasis 0 +
    ((Complex.I • (lowInputAngularCurve parameters lower length positive mode radius • first)) 0) • operatorBasis 1 +
    ((Complex.I • (lowInputCellCurve parameters lower length positive mode radius • first)) 0) • operatorBasis 2 +
    ((lowInputRadiusCurve parameters lower length positive mode radius • first) 0) • operatorBasis 3

/-- Literal coefficient identity of the seven-component low packet. -/
theorem lowNormalizedSevenInput_ae (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) (mode : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowNormalizedSevenInput parameters lower length lengthPositive positive field mode.val radius =
        lowSevenInputSymbol parameters lower length positive mode radius (field (0, mode) radius) (field (1, mode) radius) := by
  let first := lowBulkSlot (dimension := 7) lower 0 (lowComponent lower 1 field)
  let angular := lowBulkSlot (dimension := 7) lower 1 (lowNormalizedAngular parameters lower length positive field)
  let cell := lowBulkSlot (dimension := 7) lower 2 (lowNormalizedCell parameters lower length lengthPositive positive field)
  let radial := lowBulkSlot (dimension := 7) lower 3 (lowNormalizedRadius parameters lower length positive field)
  have firstLaw := lowBulkSlot_ae (dimension := 7) lower 0 (lowComponent lower 1 field)
  have angularLaw := lowBulkSlot_ae (dimension := 7) lower 1 (lowNormalizedAngular parameters lower length positive field)
  have cellLaw := lowBulkSlot_ae (dimension := 7) lower 2 (lowNormalizedCell parameters lower length lengthPositive positive field)
  have radialLaw := lowBulkSlot_ae (dimension := 7) lower 3 (lowNormalizedRadius parameters lower length positive field)
  filter_upwards [firstLaw, angularLaw, cellLaw, radialLaw,
    lowNormalizedAngular_ae parameters lower length positive field mode,
    lowNormalizedCell_ae parameters lower length lengthPositive positive field mode,
    lowNormalizedRadius_ae parameters lower length positive field mode,
    Lp.coeFn_add ((first mode.val + angular mode.val) + cell mode.val) (radial mode.val),
    Lp.coeFn_add (first mode.val + angular mode.val) (cell mode.val),
    Lp.coeFn_add (first mode.val) (angular mode.val)]
    with radius firstLaw angularLaw cellLaw radialLaw angularValue cellValue radialValue totalSum partialSum firstSum
  change ((first mode.val + angular mode.val) + cell mode.val + radial mode.val) radius = _
  rw [totalSum]
  simp only [Pi.add_apply]
  rw [partialSum]
  simp only [Pi.add_apply]
  rw [firstSum]
  simp only [Pi.add_apply]
  change ((lowBulkSlot lower 0 (lowComponent lower 1 field) mode.val radius +
    lowBulkSlot lower 1 (lowNormalizedAngular parameters lower length positive field) mode.val radius) +
    lowBulkSlot lower 2 (lowNormalizedCell parameters lower length lengthPositive positive field) mode.val radius) +
    lowBulkSlot lower 3 (lowNormalizedRadius parameters lower length positive field) mode.val radius = _
  rw [firstLaw mode, angularLaw mode, cellLaw mode, radialLaw mode, angularValue, cellValue, radialValue]
  rfl

theorem lowSevenInputSymbol_component (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (mode : LowAnnularMode) (radius : ℝ) (first second : ComplexEuclidean 1) (slot : Fin 7) :
    lowSevenInputSymbol parameters lower length positive mode radius first second slot =
      if slot = 0 then second 0 else
      if slot = 1 then Complex.I * (lowInputAngularCurve parameters lower length positive mode radius : ℂ) * first 0 else
      if slot = 2 then Complex.I * (lowInputCellCurve parameters lower length positive mode radius : ℂ) * first 0 else
      if slot = 3 then (lowInputRadiusCurve parameters lower length positive mode radius : ℂ) * first 0 else 0 := by
  fin_cases slot <;> simp [lowSevenInputSymbol, operatorBasis, Complex.real_smul, mul_assoc]

end Grad.AnnularCurrentLow
