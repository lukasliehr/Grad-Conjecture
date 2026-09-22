import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.AddCircle.Defs

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.ClosedJets

abbrev SpatialPlane := EuclideanSpace ℝ (Fin 2)
abbrev SpatialCell := EuclideanSpace ℝ (Fin 3)
abbrev ComplexEuclidean (dimension : ℕ) := EuclideanSpace ℂ (Fin dimension)

def openUnitDisk : Set SpatialPlane := {point | ‖point‖ < 1}

def closedUnitDisk : Set SpatialPlane := {point | ‖point‖ ≤ 1}

abbrev ClosedDisk := {point : SpatialPlane // point ∈ closedUnitDisk}

abbrev OpenDisk := {point : SpatialPlane // point ∈ openUnitDisk}

theorem openDiskMembershipClosed (point : SpatialPlane) (membership : point ∈ openUnitDisk) :
    point ∈ closedUnitDisk := by
  change ‖point‖ < 1 at membership
  change ‖point‖ ≤ 1
  exact membership.le

def openDiskInclusion : OpenDisk → ClosedDisk := fun point =>
  ⟨point.val, openDiskMembershipClosed point.val point.property⟩

def closedDiskLift {Target : Type*} [Zero Target]
    (function : ClosedDisk → Target) (point : SpatialPlane) : Target := by
  classical
  exact if membership : point ∈ closedUnitDisk then function ⟨point, membership⟩ else 0

def spatialBasis (coordinate : Fin 2) : SpatialPlane :=
  WithLp.toLp 2 (Pi.single coordinate 1)

abbrev CartesianWord (order : ℕ) := Fin order → Fin 2

abbrev CartesianMultiIndex := ℕ × ℕ

def cartesianOrder (index : CartesianMultiIndex) : ℕ := index.1 + index.2

def cartesianMultiIndexWord (index : CartesianMultiIndex) : CartesianWord (cartesianOrder index) :=
  fun position => if position.val < index.1 then 0 else 1

def emptyCartesianWord : CartesianWord 0 := fun coordinate => Fin.elim0 coordinate

def cartesianDerivative {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (order : ℕ) (word : CartesianWord order) (function : SpatialPlane → Target)
    (point : SpatialPlane) : Target :=
  iteratedFDeriv ℝ order function point (fun position => spatialBasis (word position))

def cartesianMultiDerivative {Target : Type*}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (index : CartesianMultiIndex) (function : SpatialPlane → Target) (point : SpatialPlane) : Target :=
  cartesianDerivative (cartesianOrder index) (cartesianMultiIndexWord index) function point

def IsCartesianExtension {dimension : ℕ}
    (value : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (order : ℕ) (word : CartesianWord order)
    (extension : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) : Prop :=
  ∀ point : ClosedDisk, point.val ∈ openUnitDisk →
    extension point = cartesianDerivative order word (closedDiskLift value) point.val

structure ClosedJet (dimension : ℕ) where
  value : ContinuousMap ClosedDisk (ComplexEuclidean dimension)
  smoothInterior : ContDiffOn ℝ ∞ (closedDiskLift value) openUnitDisk
  derivativeExists : ∀ order word, ∃ extension, IsCartesianExtension value order word extension

instance (dimension : ℕ) : CoeFun (ClosedJet dimension)
    (fun _ => ClosedDisk → ComplexEuclidean dimension) := ⟨fun field => field.value⟩

def closedDerivative {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
  Classical.choose (field.derivativeExists order word)

def closedMultiDerivative {dimension : ℕ} (field : ClosedJet dimension)
    (index : CartesianMultiIndex) : ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
  closedDerivative field (cartesianOrder index) (cartesianMultiIndexWord index)

def IsValuewiseZero {dimension : ℕ} (field : ClosedJet dimension) : Prop :=
  ∀ point, field.value point = 0

def IsValuewiseAdd {dimension : ℕ}
    (sum first second : ClosedJet dimension) : Prop :=
  ∀ point, sum.value point = first.value point + second.value point

def IsValuewiseSmul {dimension : ℕ} (scalar : ℂ)
    (scaled field : ClosedJet dimension) : Prop :=
  ∀ point, scaled.value point = scalar • field.value point

abbrev CellCircle := AddCircle (2 * Real.pi)
abbrev DiskCellDomain := ClosedDisk × CellCircle

def planarPart (point : SpatialCell) : SpatialPlane :=
  WithLp.toLp 2 ![point 0, point 1]

def openUnitCylinder : Set SpatialCell := {point | ‖planarPart point‖ < 1}

def closedUnitCylinder : Set SpatialCell := {point | ‖planarPart point‖ ≤ 1}

theorem openCylinderMembershipClosed (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    point ∈ closedUnitCylinder := by
  change ‖planarPart point‖ < 1 at membership
  change ‖planarPart point‖ ≤ 1
  exact membership.le

def diskCellPoint (point : SpatialCell) (membership : point ∈ closedUnitCylinder) :
    DiskCellDomain :=
  (⟨planarPart point, membership⟩, (point 2 : CellCircle))

def diskCellLift {Target : Type*} [Zero Target]
    (function : DiskCellDomain → Target) (point : SpatialCell) : Target := by
  classical
  exact if membership : point ∈ closedUnitCylinder then
    function (diskCellPoint point membership) else 0

def spatialCellBasis (coordinate : Fin 3) : SpatialCell :=
  WithLp.toLp 2 (Pi.single coordinate 1)

abbrev MixedCartesianWord (order : ℕ) := Fin order → Fin 3

abbrev DiskCellMultiIndex := (ℕ × ℕ) × ℕ

def diskCellOrder (index : DiskCellMultiIndex) : ℕ := index.1.1 + index.1.2 + index.2

def diskCellMultiIndexWord (index : DiskCellMultiIndex) :
    MixedCartesianWord (diskCellOrder index) := fun position =>
  if position.val < index.1.1 then 0 else if position.val < index.1.1 + index.1.2 then 1 else 2

def emptyMixedCartesianWord : MixedCartesianWord 0 := fun coordinate => Fin.elim0 coordinate

def mixedCartesianDerivative {Target : Type*}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (order : ℕ) (word : MixedCartesianWord order) (function : SpatialCell → Target)
    (point : SpatialCell) : Target :=
  iteratedFDeriv ℝ order function point (fun position => spatialCellBasis (word position))

def diskCellMultiDerivative {Target : Type*}
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (index : DiskCellMultiIndex) (function : SpatialCell → Target) (point : SpatialCell) : Target :=
  mixedCartesianDerivative (diskCellOrder index) (diskCellMultiIndexWord index) function point

def IsMixedCartesianExtension {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (order : ℕ) (word : MixedCartesianWord order)
    (extension : ContinuousMap DiskCellDomain (ComplexEuclidean dimension)) : Prop :=
  ∀ (point : SpatialCell) (membership : point ∈ openUnitCylinder),
    extension (diskCellPoint point (openCylinderMembershipClosed point membership)) =
      mixedCartesianDerivative order word (diskCellLift value) point

structure DiskCellClosedJet (dimension : ℕ) where
  value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension)
  smoothInterior : ContDiffOn ℝ ∞ (diskCellLift value) openUnitCylinder
  derivativeExists : ∀ order word, ∃ extension, IsMixedCartesianExtension value order word extension

instance (dimension : ℕ) : CoeFun (DiskCellClosedJet dimension)
    (fun _ => DiskCellDomain → ComplexEuclidean dimension) := ⟨fun field => field.value⟩

def closedMixedDerivative {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) :=
  Classical.choose (field.derivativeExists order word)

def closedDiskCellMultiDerivative {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : DiskCellMultiIndex) : ContinuousMap DiskCellDomain (ComplexEuclidean dimension) :=
  closedMixedDerivative field (diskCellOrder index) (diskCellMultiIndexWord index)

def IsDiskCellValuewiseZero {dimension : ℕ} (field : DiskCellClosedJet dimension) : Prop :=
  ∀ point, field.value point = 0

def IsDiskCellValuewiseAdd {dimension : ℕ}
    (sum first second : DiskCellClosedJet dimension) : Prop :=
  ∀ point, sum.value point = first.value point + second.value point

def IsDiskCellValuewiseSmul {dimension : ℕ} (scalar : ℂ)
    (scaled field : DiskCellClosedJet dimension) : Prop :=
  ∀ point, scaled.value point = scalar • field.value point

abbrev OpenDiskCell := OpenDisk × CellCircle

def openDiskCellInclusion : OpenDiskCell → DiskCellDomain := fun point =>
  (openDiskInclusion point.1, point.2)

def DiskTopologyGoal : Prop :=
  openUnitDisk ⊆ closedUnitDisk ∧ DenseRange openDiskInclusion

def ClosedJetGoal : Prop :=
  (∀ (dimension : ℕ) (first second : ClosedJet dimension),
    first.value = second.value → first = second) ∧
  (∀ (dimension : ℕ) (field : ClosedJet dimension) order word,
    IsCartesianExtension field.value order word (closedDerivative field order word) ∧
    ∀ extension, IsCartesianExtension field.value order word extension →
      extension = closedDerivative field order word) ∧
  (∀ (dimension : ℕ) (field : ClosedJet dimension),
    closedDerivative field 0 emptyCartesianWord = field.value)

def ClosedJetLinearGoal : Prop :=
  (∀ dimension, ∃! zero : ClosedJet dimension, IsValuewiseZero zero) ∧
  (∀ dimension (first second : ClosedJet dimension),
    ∃! sum, IsValuewiseAdd sum first second) ∧
  (∀ dimension (scalar : ℂ) (field : ClosedJet dimension),
    ∃! scaled, IsValuewiseSmul scalar scaled field) ∧
  (∀ dimension (first second sum : ClosedJet dimension), IsValuewiseAdd sum first second →
    ∀ order word point, closedDerivative sum order word point =
      closedDerivative first order word point + closedDerivative second order word point) ∧
  (∀ dimension (scalar : ℂ) (field scaled : ClosedJet dimension),
    IsValuewiseSmul scalar scaled field → ∀ order word point,
      closedDerivative scaled order word point = scalar • closedDerivative field order word point)

def DiskCellTopologyGoal : Prop := DenseRange openDiskCellInclusion

def DiskCellClosedJetGoal : Prop :=
  (∀ (dimension : ℕ) (first second : DiskCellClosedJet dimension),
    first.value = second.value → first = second) ∧
  (∀ (dimension : ℕ) (field : DiskCellClosedJet dimension) order word,
    IsMixedCartesianExtension field.value order word (closedMixedDerivative field order word) ∧
    ∀ extension, IsMixedCartesianExtension field.value order word extension →
      extension = closedMixedDerivative field order word) ∧
  (∀ (dimension : ℕ) (field : DiskCellClosedJet dimension),
    closedMixedDerivative field 0 emptyMixedCartesianWord = field.value)

def DiskCellLinearGoal : Prop :=
  (∀ dimension, ∃! zero : DiskCellClosedJet dimension, IsDiskCellValuewiseZero zero) ∧
  (∀ dimension (first second : DiskCellClosedJet dimension),
    ∃! sum, IsDiskCellValuewiseAdd sum first second) ∧
  (∀ dimension (scalar : ℂ) (field : DiskCellClosedJet dimension),
    ∃! scaled, IsDiskCellValuewiseSmul scalar scaled field) ∧
  (∀ dimension (first second sum : DiskCellClosedJet dimension),
    IsDiskCellValuewiseAdd sum first second → ∀ order word,
      ∀ point, closedMixedDerivative sum order word point =
        closedMixedDerivative first order word point + closedMixedDerivative second order word point) ∧
  (∀ dimension (scalar : ℂ) (field scaled : DiskCellClosedJet dimension),
    IsDiskCellValuewiseSmul scalar scaled field → ∀ order word point,
      closedMixedDerivative scaled order word point = scalar • closedMixedDerivative field order word point)

def BlockGoal : Prop :=
  DiskTopologyGoal ∧ ClosedJetGoal ∧ ClosedJetLinearGoal ∧
    DiskCellTopologyGoal ∧ DiskCellClosedJetGoal ∧ DiskCellLinearGoal

end Grad.ClosedJets
