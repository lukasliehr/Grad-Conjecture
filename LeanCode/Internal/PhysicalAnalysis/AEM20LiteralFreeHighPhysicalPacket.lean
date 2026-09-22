import AEM19ExactHighLowPhysicalStorage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularOmegaGraph Grad.AnnularTiltedReference Grad.SourceCollarCoefficients Grad.PhaseAlgebra
open Grad.CircularHighRegularity Grad.GaugeCoefficients.Physical.Ledger

/-- Actual scalar seven-slot physical symbol, before all coefficient kernels. -/
def crossSevenSymbol (radius : ℝ) (mode : ℤ × ℤ) (xi x : ComplexEuclidean 1) : ComplexEuclidean 7 :=
  x 0 • operatorBasis 0 +
    (Complex.I * (mode.1 : ℂ) * (radius⁻¹ : ℝ) * xi 0) • operatorBasis 1 +
    (Complex.I * (mode.2 : ℂ) * xi 0) • operatorBasis 2 +
    ((radius⁻¹ : ℝ) * xi 0) • operatorBasis 3

theorem crossSevenSymbol_smul (radius : ℝ) (mode : ℤ × ℤ) (xi x : ComplexEuclidean 1) (scalar : ℂ) :
    crossSevenSymbol radius mode (scalar • xi) (scalar • x) = scalar • crossSevenSymbol radius mode xi x := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [crossSevenSymbol, operatorBasis] <;> ring

theorem highCrossSevenInput_same (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) :
    highCrossSevenInput lower length positive lengthPositive field =
      highSevenEnergyPacket lower length positive
        (highBulkIntoFull lower (crossHighX lower length positive lengthPositive field),
          crossHighW lower length positive lengthPositive field) := rfl

theorem highCrossCell_mode (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ((length : ℂ) • highEnergyCell lower length positive field) mode =
      (Complex.I * (mode.val.2 : ℂ)) • annularEnergyValue lower length positive field mode := by
  change (length : ℂ) • highEnergyCell lower length positive field mode = _
  rw [highEnergyCell_mode, smul_smul]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr lengthPositive.ne']

/-- Literal stored slot assembly, kept separate from physical decoding. -/
theorem freeHighSevenPacket_slots_ae (lower length : ℝ) (positive : 0 < lower)
    (flux : AnnularBulk lower) (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      highSevenEnergyPacket lower length positive (highBulkIntoFull lower flux, field) mode.val radius =
        (flux mode radius 0) • operatorBasis 0 +
        (highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive field) mode radius 0) • operatorBasis 1 +
        (((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive field)) mode radius 0) • operatorBasis 2 +
        (highEnergyRadius lower length positive (bEnergyDecode lower length positive field) mode radius 0) • operatorBasis 3 := by
  let decoded := bEnergyDecode lower length positive field
  let first := highBulkSlot (dimension := 7) lower 0 flux
  let angular := highBulkSlot (dimension := 7) lower 1 (highEnergyAngularRadius lower length positive decoded)
  let cell := highBulkSlot (dimension := 7) lower 2 ((length : ℂ) • highEnergyCell lower length positive decoded)
  let radial := highBulkSlot (dimension := 7) lower 3 (highEnergyRadius lower length positive decoded)
  filter_upwards [highBulkSlot_ae (dimension := 7) lower 0 flux,
    highBulkSlot_ae (dimension := 7) lower 1 (highEnergyAngularRadius lower length positive decoded),
    highBulkSlot_ae (dimension := 7) lower 2 ((length : ℂ) • highEnergyCell lower length positive decoded),
    highBulkSlot_ae (dimension := 7) lower 3 (highEnergyRadius lower length positive decoded),
    Lp.coeFn_add ((first mode.val + angular mode.val) + cell mode.val) (radial mode.val),
    Lp.coeFn_add (first mode.val + angular mode.val) (cell mode.val),
    Lp.coeFn_add (first mode.val) (angular mode.val)]
    with radius firstLaw angularLaw cellLaw radialLaw totalSum partialSum firstSum
  change ((first mode.val + angular mode.val) + cell mode.val + radial mode.val) radius = _
  rw [totalSum]
  simp only [Pi.add_apply]
  rw [partialSum]
  simp only [Pi.add_apply]
  rw [firstSum]
  simp only [Pi.add_apply]
  change ((highBulkSlot lower 0 flux mode.val radius +
    highBulkSlot lower 1 (highEnergyAngularRadius lower length positive decoded) mode.val radius) +
    highBulkSlot lower 2 ((length : ℂ) • highEnergyCell lower length positive decoded) mode.val radius) +
    highBulkSlot lower 3 (highEnergyRadius lower length positive decoded) mode.val radius = _
  exact congrArg₂ (fun x y : ComplexEuclidean 7 => x + y)
    (congrArg₂ (fun x y : ComplexEuclidean 7 => x + y)
      (congrArg₂ (fun x y : ComplexEuclidean 7 => x + y) (firstLaw mode) (angularLaw mode))
      (cellLaw mode)) (radialLaw mode)

/-- The completed packet contains free x and literal Rxi/r, xi_zeta, xi/r. -/
theorem freeHighSevenPacket_ae (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (flux : AnnularBulk lower) (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      highSevenEnergyPacket lower length positive (highBulkIntoFull lower flux, field) mode.val radius =
        crossSevenSymbol radius mode.val
          (annularEnergyValue lower length positive (bEnergyDecode lower length positive field) mode radius)
          (flux mode radius) := by
  let decoded := bEnergyDecode lower length positive field
  let value := annularEnergyValue lower length positive decoded mode
  have angularIdentity := highEnergyAngularRadius_mode lower length positive decoded mode
  have radialIdentity := highEnergyRadius_mode lower length positive decoded mode
  have cellIdentity := highCrossCell_mode lower length positive lengthPositive decoded mode
  filter_upwards [freeHighSevenPacket_slots_ae lower length positive flux field mode,
    Lp.coeFn_smul (Complex.I * (mode.val.1 : ℂ)) (highEnergyRadius lower length positive decoded mode),
    Lp.coeFn_smul (Complex.I * (mode.val.2 : ℂ)) value,
    collarScalar_ae 1 lower (highReciprocalRadius lower positive) value,
    ae_restrict_mem measurableSet_Icc]
    with radius packet angularScaled cellScaled radialScaled inside
  rw [packet]
  change (flux mode radius 0) • operatorBasis 0 +
    (highEnergyAngularRadius lower length positive decoded mode radius 0) • operatorBasis 1 +
    (((length : ℂ) • highEnergyCell lower length positive decoded) mode radius 0) • operatorBasis 2 +
    (highEnergyRadius lower length positive decoded mode radius 0) • operatorBasis 3 =
    crossSevenSymbol radius mode.val (value radius) (flux mode radius)
  have radialAt : highEnergyRadius lower length positive decoded mode radius =
      radius⁻¹ • value radius := by
    rw [radialIdentity]
    change (collarScalar 1 lower (highReciprocalRadius lower positive) value) radius =
      (max lower radius)⁻¹ • value radius at radialScaled
    rw [max_eq_right inside.1] at radialScaled
    exact radialScaled
  rw [angularIdentity, angularScaled, cellIdentity, cellScaled]
  simp only [Pi.smul_apply, radialAt]
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [crossSevenSymbol, operatorBasis, Complex.real_smul]
  ring

theorem highCrossSevenInput_ae (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      highCrossSevenInput lower length positive lengthPositive field mode.val radius =
        crossSevenSymbol radius mode.val
          (annularEnergyValue lower length positive (bEnergyDecode lower length positive
            (crossHighW lower length positive lengthPositive field)) mode radius)
          (crossHighX lower length positive lengthPositive field mode radius) := by
  rw [highCrossSevenInput_same]
  exact freeHighSevenPacket_ae lower length positive lengthPositive
    (crossHighX lower length positive lengthPositive field) (crossHighW lower length positive lengthPositive field) mode

end Grad.AnnularCrossMaps
