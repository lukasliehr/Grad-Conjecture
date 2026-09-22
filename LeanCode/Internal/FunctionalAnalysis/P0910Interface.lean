import COR01Proof
import DE1Proof
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

instance spatialPeriodPositive : Fact (0 < (4 : ℝ)) := ⟨by norm_num⟩
instance cellPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

abbrev SpatialCircle := AddCircle (4 : ℝ)
abbrev SpatialTorus := SpatialCircle × SpatialCircle
abbrev TorusCellDomain := SpatialTorus × CellCircle

def spatialProbabilityMeasure : Measure SpatialCircle :=
  (ENNReal.ofReal 4)⁻¹ • AddCircle.haarAddCircle

def cellProbabilityMeasure : Measure CellCircle :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • AddCircle.haarAddCircle

def torusCellPoint (point : SpatialCell) : TorusCellDomain :=
  (((point 0 : SpatialCircle), (point 1 : SpatialCircle)), (point 2 : CellCircle))

def torusCellLift {Target : Type*}
    (function : TorusCellDomain → Target) (point : SpatialCell) : Target :=
  function (torusCellPoint point)

def spatialTorusRepresentative (point : SpatialTorus) : SpatialPlane :=
  WithLp.toLp 2 ![(AddCircle.equivIco (4 : ℝ) (-2) point.1).val,
    (AddCircle.equivIco (4 : ℝ) (-2) point.2).val]

def diskToTorus (point : DiskCellDomain) : TorusCellDomain :=
  (((point.1.val 0 : SpatialCircle), (point.1.val 1 : SpatialCircle)), point.2)

structure TorusSmoothField (dimension : ℕ) where
  value : ContinuousMap TorusCellDomain (ComplexEuclidean dimension)
  smoothLift : ContDiff ℝ ∞ (torusCellLift value)
  derivativeExists : ∀ order word, ∃ extension :
    ContinuousMap TorusCellDomain (ComplexEuclidean dimension),
      ∀ point : SpatialCell,
        extension (torusCellPoint point) =
          mixedCartesianDerivative order word (torusCellLift value) point

instance (dimension : ℕ) : CoeFun (TorusSmoothField dimension)
    (fun _ => TorusCellDomain → ComplexEuclidean dimension) :=
  ⟨fun field => field.value⟩

def torusDerivative {dimension : ℕ} (field : TorusSmoothField dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    ContinuousMap TorusCellDomain (ComplexEuclidean dimension) :=
  Classical.choose (field.derivativeExists order word)

def torusDiskCellMultiDerivative {dimension : ℕ} (field : TorusSmoothField dimension)
    (index : DiskCellMultiIndex) :
    ContinuousMap TorusCellDomain (ComplexEuclidean dimension) :=
  torusDerivative field (diskCellOrder index) (diskCellMultiIndexWord index)

def pureCellWord (order : ℕ) : MixedCartesianWord order := fun _ => 2

def collarWidth : ℝ := 1 / 4
def cutoffPlateauWidth : ℝ := collarWidth / 3
def cutoffSupportWidth : ℝ := 2 * collarWidth / 3
def innerCollarRadius : ℝ := 1 - collarWidth
def outerSupportRadius : ℝ := 1 + cutoffSupportWidth

/-- A fixed explicit smooth cutoff: one through `a/3` and zero from `2a/3` onward. -/
def plateauCutoff (scale : ℝ) : ℝ :=
  1 - Real.smoothTransition (12 * scale - 1)

def reflectedPoint (index : ℕ) (point : SpatialPlane) : SpatialPlane :=
  (1 - node index * (‖point‖ - 1)) • (‖point‖⁻¹ • point)

def exteriorSummandFromValue {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle) :
    ComplexEuclidean dimension :=
  (((coefficient index * plateauCutoff (node index * (‖point‖ - 1)) : ℝ) : ℂ) •
    closedDiskLift (fun diskPoint => value (diskPoint, cell)) (reflectedPoint index point))

def exteriorSeriesFromValue {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) : ComplexEuclidean dimension :=
  ∑' index, exteriorSummandFromValue value index point cell

def ambientExtensionFromValue {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) : ComplexEuclidean dimension := by
  classical
  exact if membership : point ∈ closedUnitDisk then value (⟨point, membership⟩, cell)
    else exteriorSeriesFromValue value point cell

def ambientExtensionCellLift {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) : ComplexEuclidean dimension :=
  ambientExtensionFromValue field.value (planarPart point) (point 2 : CellCircle)

def periodizedExtensionFromValue {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : TorusCellDomain) : ComplexEuclidean dimension :=
  ambientExtensionFromValue value (spatialTorusRepresentative point.1) point.2

def openPeriodSquare : Set SpatialPlane :=
  {point | -2 < point 0 ∧ point 0 < 2 ∧ -2 < point 1 ∧ point 1 < 2}

def fundamentalHalfOpenSquare : Set SpatialPlane :=
  {point | -2 ≤ point 0 ∧ point 0 < 2 ∧ -2 ≤ point 1 ∧ point 1 < 2}

def gluingCollar : Set SpatialCell :=
  {point | innerCollarRadius < ‖planarPart point‖ ∧
    ‖planarPart point‖ < outerSupportRadius}

def diskCellMultiIndices (grade : ℕ) : Finset DiskCellMultiIndex :=
  ((((Finset.range (grade + 1)).product (Finset.range (grade + 1))).product
    (Finset.range (grade + 1))).filter fun index => diskCellOrder index ≤ grade)

def diskDerivativeEnergy {dimension : ℕ} (grade : ℕ)
    (field : DiskCellClosedJet dimension) : ℝ :=
  ∑ index ∈ diskCellMultiIndices grade,
    ∫ cell : CellCircle, ∫ point : SpatialPlane,
      ‖closedDiskLift
        (fun diskPoint => closedDiskCellMultiDerivative field index (diskPoint, cell)) point‖ ^ 2
      ∂volume ∂cellProbabilityMeasure

def torusDerivativeEnergy {dimension : ℕ} (grade : ℕ)
    (field : TorusSmoothField dimension) : ℝ :=
  ∑ index ∈ diskCellMultiIndices grade,
    ∫ cell : CellCircle, ∫ second : SpatialCircle, ∫ first : SpatialCircle,
      ‖torusDiskCellMultiDerivative field index ((first, second), cell)‖ ^ 2
      ∂spatialProbabilityMeasure ∂spatialProbabilityMeasure ∂cellProbabilityMeasure

def diskDerivativeGrade {dimension : ℕ} (grade : ℕ)
    (field : DiskCellClosedJet dimension) : ℝ :=
  Real.sqrt (diskDerivativeEnergy grade field)

def torusDerivativeGrade {dimension : ℕ} (grade : ℕ)
    (field : TorusSmoothField dimension) : ℝ :=
  Real.sqrt (torusDerivativeEnergy grade field)

def IsRealVector {dimension : ℕ} (value : ComplexEuclidean dimension) : Prop :=
  ∀ coordinate, star (value coordinate) = value coordinate

def IsRealDiskCellField {dimension : ℕ} (field : DiskCellClosedJet dimension) : Prop :=
  ∀ point, IsRealVector (field.value point)

def IsRealTorusField {dimension : ℕ} (field : TorusSmoothField dimension) : Prop :=
  ∀ point, IsRealVector (field.value point)

def IsTorusValuewiseAdd {dimension : ℕ}
    (sum first second : TorusSmoothField dimension) : Prop :=
  ∀ point, sum.value point = first.value point + second.value point

def IsTorusValuewiseSmul {dimension : ℕ} (scalar : ℂ)
    (scaled field : TorusSmoothField dimension) : Prop :=
  ∀ point, scaled.value point = scalar • field.value point

structure OrdinaryExtensionRetraction where
  extension : ∀ dimension, DiskCellClosedJet dimension → TorusSmoothField dimension
  restriction : ∀ dimension, TorusSmoothField dimension → DiskCellClosedJet dimension

def PlateauGoal : Prop :=
  ContDiff ℝ ∞ plateauCutoff ∧
  (∀ scale, 0 ≤ plateauCutoff scale ∧ plateauCutoff scale ≤ 1) ∧
  (∀ scale, scale ≤ cutoffPlateauWidth → plateauCutoff scale = 1) ∧
  (∀ scale, cutoffSupportWidth ≤ scale → plateauCutoff scale = 0) ∧
  (∀ order, 0 < order → iteratedDeriv order plateauCutoff 0 = 0) ∧
  (∀ order, ∃ bound : ℝ, 0 ≤ bound ∧
    ∀ scale, ‖iteratedDeriv order plateauCutoff scale‖ ≤ bound)

def ConstructionFormulaGoal (data : OrdinaryExtensionRetraction) : Prop :=
  (∀ dimension (field : DiskCellClosedJet dimension) point,
    (data.extension dimension field).value point =
      periodizedExtensionFromValue field.value point) ∧
  (∀ dimension (field : TorusSmoothField dimension) point,
    (data.restriction dimension field).value point = field.value (diskToTorus point))

def SmoothBoundarySupportGoal (data : OrdinaryExtensionRetraction) : Prop :=
  ∀ dimension (field : DiskCellClosedJet dimension),
    ContDiff ℝ ∞ (ambientExtensionCellLift field) ∧
    ContDiffOn ℝ ∞ (ambientExtensionCellLift field) gluingCollar ∧
    (∀ (point : SpatialPlane) (membership : point ∈ closedUnitDisk) (cell : CellCircle),
      ambientExtensionFromValue field.value point cell = field.value (⟨point, membership⟩, cell)) ∧
    (∀ (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) order word,
      mixedCartesianDerivative order word (ambientExtensionCellLift field) point =
        closedMixedDerivative field order word
          (diskCellPoint point (by change ‖planarPart point‖ ≤ 1; exact boundary.le))) ∧
    (∀ (point : SpatialPlane) (cell : CellCircle), outerSupportRadius ≤ ‖point‖ →
      ambientExtensionFromValue field.value point cell = 0) ∧
    (∀ cell : CellCircle,
      tsupport (fun point => ambientExtensionFromValue field.value point cell) ⊆ openPeriodSquare) ∧
    (∀ (point : SpatialPlane) (cell : ℝ), point ∈ fundamentalHalfOpenSquare →
      torusCellLift (data.extension dimension field).value
          (assembleSpatialCell point cell) =
        ambientExtensionFromValue field.value point (cell : CellCircle))

def RetractionLinearityRealGoal (data : OrdinaryExtensionRetraction) : Prop :=
  (∀ dimension (field : DiskCellClosedJet dimension),
    data.restriction dimension (data.extension dimension field) = field) ∧
  (∀ dimension (first second : DiskCellClosedJet dimension) point,
    (data.extension dimension (diskCellClosedJetAdd first second)).value point =
      (data.extension dimension first).value point +
        (data.extension dimension second).value point) ∧
  (∀ dimension (scalar : ℂ) (field : DiskCellClosedJet dimension) point,
    (data.extension dimension (diskCellClosedJetSmul scalar field)).value point =
      scalar • (data.extension dimension field).value point) ∧
  (∀ dimension (sum first second : TorusSmoothField dimension),
    IsTorusValuewiseAdd sum first second →
      IsDiskCellValuewiseAdd (data.restriction dimension sum)
        (data.restriction dimension first) (data.restriction dimension second)) ∧
  (∀ dimension (scalar : ℂ) (scaled field : TorusSmoothField dimension),
    IsTorusValuewiseSmul scalar scaled field →
      IsDiskCellValuewiseSmul scalar (data.restriction dimension scaled)
        (data.restriction dimension field)) ∧
  (∀ dimension (field : DiskCellClosedJet dimension), IsRealDiskCellField field →
    IsRealTorusField (data.extension dimension field)) ∧
  (∀ dimension (field : TorusSmoothField dimension), IsRealTorusField field →
    IsRealDiskCellField (data.restriction dimension field))

def CellDerivativeCommutationGoal (data : OrdinaryExtensionRetraction) : Prop :=
  (∀ dimension (field : DiskCellClosedJet dimension) order point,
    torusDerivative (data.extension dimension field) order (pureCellWord order) point =
      periodizedExtensionFromValue
        (closedMixedDerivative field order (pureCellWord order)) point) ∧
  (∀ dimension (field : TorusSmoothField dimension) order point,
    closedMixedDerivative (data.restriction dimension field) order (pureCellWord order) point =
      torusDerivative field order (pureCellWord order) (diskToTorus point))

def SameGradeBoundGoal (data : OrdinaryExtensionRetraction) : Prop :=
  ∀ grade : ℕ, ∃ constant : ℝ, 0 ≤ constant ∧
    (∀ dimension (field : DiskCellClosedJet dimension),
      torusDerivativeGrade grade (data.extension dimension field) ≤
        constant * diskDerivativeGrade grade field) ∧
    (∀ dimension (field : TorusSmoothField dimension),
      diskDerivativeGrade grade (data.restriction dimension field) ≤
        constant * torusDerivativeGrade grade field)

def OperatorGoal (data : OrdinaryExtensionRetraction) : Prop :=
  ConstructionFormulaGoal data ∧ SmoothBoundarySupportGoal data ∧
    RetractionLinearityRealGoal data ∧ CellDerivativeCommutationGoal data ∧
    SameGradeBoundGoal data

def BlockGoal : Prop := PlateauGoal ∧ ∃ data : OrdinaryExtensionRetraction, OperatorGoal data

end Grad.DiskExtension.Operator
