import GC8Proof
import COR01Proof
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

instance closedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

/-- Cartesian multi-indices of total order at most `grade`.  Both Cartesian
coordinates are retained; this is the literal `|alpha| <= q` index set in AP8. -/
abbrev DerivativeIndex (grade : ℕ) :=
  { index : Fin (grade + 1) × Fin (grade + 1) //
    (index.1 : ℕ) + (index.2 : ℕ) ≤ grade }

def derivativeOrder {grade : ℕ} (index : DerivativeIndex grade) : ℕ :=
  (index.1.1 : ℕ) + (index.1.2 : ℕ)

def derivativeMultiIndex {grade : ℕ} (index : DerivativeIndex grade) :
    CartesianMultiIndex :=
  ((index.1.1 : ℕ), (index.1.2 : ℕ))

def zeroDerivativeIndex : DerivativeIndex 0 :=
  ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), by omega⟩

/-- A split `beta <= alpha`, retaining both Cartesian coordinates. -/
abbrev DerivativeSplit {grade : ℕ} (index : DerivativeIndex grade) :=
  Fin ((index.1.1 : ℕ) + 1) × Fin ((index.1.2 : ℕ) + 1)

def lowerDerivativeIndex {grade : ℕ} (index : DerivativeIndex grade)
    (split : DerivativeSplit index) : DerivativeIndex grade := by
  have firstLe : (split.1 : ℕ) ≤ (index.1.1 : ℕ) := Nat.lt_succ_iff.mp split.1.isLt
  have secondLe : (split.2 : ℕ) ≤ (index.1.2 : ℕ) := Nat.lt_succ_iff.mp split.2.isLt
  refine ⟨(⟨(split.1 : ℕ), lt_of_le_of_lt firstLe index.1.1.isLt⟩,
    ⟨(split.2 : ℕ), lt_of_le_of_lt secondLe index.1.2.isLt⟩), ?_⟩
  exact (Nat.add_le_add firstLe secondLe).trans index.2

def upperDerivativeIndex {grade : ℕ} (index : DerivativeIndex grade)
    (split : DerivativeSplit index) : DerivativeIndex grade := by
  have firstLe : (index.1.1 : ℕ) - (split.1 : ℕ) ≤ (index.1.1 : ℕ) := Nat.sub_le _ _
  have secondLe : (index.1.2 : ℕ) - (split.2 : ℕ) ≤ (index.1.2 : ℕ) := Nat.sub_le _ _
  refine ⟨(⟨(index.1.1 : ℕ) - (split.1 : ℕ), lt_of_le_of_lt firstLe index.1.1.isLt⟩,
    ⟨(index.1.2 : ℕ) - (split.2 : ℕ), lt_of_le_of_lt secondLe index.1.2.isLt⟩), ?_⟩
  exact (Nat.add_le_add firstLe secondLe).trans index.2

def splitMultiplicity {grade : ℕ} (index : DerivativeIndex grade)
    (split : DerivativeSplit index) : ℕ :=
  Nat.choose (index.1.1 : ℕ) (split.1 : ℕ) *
    Nat.choose (index.1.2 : ℕ) (split.2 : ℕ)

/-- Operator values use the induced operator norm.  Rectangular values give
the typed scalar/vector/matrix coefficient products in one carrier. -/
abbrev OperatorValue (inputDimension outputDimension : ℕ) :=
  PhysicalValue inputDimension →L[ℂ] PhysicalValue outputDimension

/-- A smooth operator-valued function on the open disk together with every
continuous closed-disk Cartesian derivative.  This is the closed-jet core,
not an ambient-extension convention. -/
def IsOperatorDerivativeExtension {inputDimension outputDimension : ℕ}
    (value : ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension))
    (index : CartesianMultiIndex)
    (extension : ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension)) : Prop :=
  ∀ point : ClosedDisk, point.val ∈ openUnitDisk →
    extension point = cartesianMultiDerivative index (closedDiskLift value) point.val

structure SmoothOperatorJet (inputDimension outputDimension : ℕ) where
  value : ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension)
  smoothInterior : ContDiffOn ℝ ∞ (closedDiskLift value) openUnitDisk
  derivativeExists : ∀ index : CartesianMultiIndex,
    ∃ extension, IsOperatorDerivativeExtension value index extension

def smoothOperatorDerivative {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  Classical.choose (field.derivativeExists index)

/-- A single `l¹` carrier over `(cell, multi-index)` gives the literal iterated
sum in AP8 while avoiding any product maximum norm.  Every integer cell,
including zero, remains in the index. -/
abbrev WeightedAmbient (grade inputDimension outputDimension : ℕ) :=
  lp (fun _ : ℤ × DerivativeIndex grade =>
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension)) 1

/-- The AP8 scale multiplying one closed derivative.  The envelope itself is
not differentiated. -/
def coefficientScale (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    (index : DerivativeIndex grade) (point : ClosedDisk) : ℝ :=
  originalEnvelope sigma gamma ell cell point.val *
    scaledCellWeight L ell cell ^ (grade - derivativeOrder index)

theorem coefficientScale_pos (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    0 < coefficientScale L sigma gamma ell grade cell index point := by
  unfold coefficientScale originalEnvelope scaledCellWeight
  exact mul_pos (Real.exp_pos _)
    (pow_pos (Real.sqrt_pos.2 (by positivity)) _)

theorem continuous_coefficientScale (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    (index : DerivativeIndex grade) :
    Continuous (coefficientScale L sigma gamma ell grade cell index) := by
  unfold coefficientScale originalEnvelope scaledCellWeight
  fun_prop

def weightedSmoothDerivative (L sigma gamma ell : ℝ) (grade : ℕ) (cell : ℤ)
    {inputDimension outputDimension : ℕ}
    (field : SmoothOperatorJet inputDimension outputDimension)
    (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point :=
    (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
      smoothOperatorDerivative field (derivativeMultiIndex index) point
  continuous_toFun := by
    exact ((Complex.continuous_ofReal.comp
      (continuous_coefficientScale L sigma gamma ell grade cell index)).smul
        (smoothOperatorDerivative field (derivativeMultiIndex index)).continuous)

/-- One finite-cell closed jet embedded with the exact AP8 scaling. -/
def weightedSingle (L sigma gamma ell : ℝ) (grade : ℕ)
    {inputDimension outputDimension : ℕ} (cell : ℤ)
    (field : SmoothOperatorJet inputDimension outputDimension) :
  WeightedAmbient grade inputDimension outputDimension :=
  ∑ index : DerivativeIndex grade,
    (lp.single 1 (cell, index)
      (weightedSmoothDerivative L sigma gamma ell grade cell field index) :
        WeightedAmbient grade inputDimension outputDimension)

/-- Finite linear combinations of one-cell smooth closed jets. -/
def smoothCore (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    Submodule ℂ (WeightedAmbient grade inputDimension outputDimension) :=
  Submodule.span ℂ (Set.range fun pair : ℤ × SmoothOperatorJet inputDimension outputDimension =>
    weightedSingle L sigma gamma ell grade pair.1 pair.2)

/-- `C_ell^q`: the completed original closed-jet graph, realized as the
closure of its finite-cell smooth core inside the literal weighted `l¹`
derivative array. -/
def Coefficient (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :=
  (smoothCore L sigma gamma ell grade inputDimension outputDimension).topologicalClosure

def coreInclusion (L sigma gamma ell : ℝ) (grade inputDimension outputDimension : ℕ) :
    smoothCore L sigma gamma ell grade inputDimension outputDimension →ₗ[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension where
  toFun core := ⟨core.1, Submodule.le_topologicalClosure _ core.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weightedDerivative {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  coefficient.1 (cell, index)

/-- The unweighted closed derivative recovered from the positive AP8 scale. -/
def coefficientDerivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point :=
    ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      weightedDerivative coefficient cell index point
  continuous_toFun := by
    have scaleContinuous : Continuous fun point : ClosedDisk =>
        (coefficientScale L sigma gamma ell grade cell index point : ℂ) :=
      Complex.continuous_ofReal.comp
        (continuous_coefficientScale L sigma gamma ell grade cell index)
    have scaleNonzero : ∀ point : ClosedDisk,
        (coefficientScale L sigma gamma ell grade cell index point : ℂ) ≠ 0 := fun point =>
      Complex.ofReal_ne_zero.mpr
        (coefficientScale_pos L sigma gamma ell grade cell index point).ne'
    exact (scaleContinuous.inv₀ scaleNonzero).smul
      (weightedDerivative coefficient cell index).continuous

def coefficientValue {L sigma gamma ell : ℝ} {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (cell : ℤ) : ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) :=
  coefficientDerivative coefficient cell zeroDerivativeIndex

/-- Uniformly convergent Fourier evaluation of a base coefficient sequence. -/
def fourierEvaluation {L sigma gamma ell : ℝ} {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (angle : ℝ) (point : ClosedDisk) : OperatorValue inputDimension outputDimension :=
  ∑' cell : ℤ, Complex.exp (Complex.I * (cell : ℂ) * angle) •
    coefficientValue coefficient cell point

/-- The literal multi-index Leibniz/convolution expression.  Composition is
typed through the intermediate physical value space and kept in written order. -/
def formalCompositionDerivative {L sigma gamma ell : ℝ}
    {grade inputDimension middleDimension outputDimension : ℕ}
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    OperatorValue inputDimension outputDimension :=
  ∑' middleCell : ℤ, ∑ split : DerivativeSplit index,
    (splitMultiplicity index split : ℂ) •
      (coefficientDerivative outer middleCell (lowerDerivativeIndex index split) point).comp
        (coefficientDerivative inner (cell - middleCell)
          (upperDerivativeIndex index split) point)

def gradeProductConstant (grade : ℕ) : ℝ :=
  (Real.sqrt 2) ^ grade *
    ∑ index : DerivativeIndex grade,
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ)

/-- Typed composition at every finite grade and every rectangular physical
value type. -/
abbrev CompositionOperation (L sigma gamma ell : ℝ) :=
  ∀ (grade inputDimension middleDimension outputDimension : ℕ),
    Coefficient L sigma gamma ell grade middleDimension outputDimension →
      Coefficient L sigma gamma ell grade inputDimension middleDimension →
      Coefficient L sigma gamma ell grade inputDimension outputDimension

abbrev IdentityOperation (L sigma gamma ell : ℝ) :=
  ∀ dimension : ℕ, Coefficient L sigma gamma ell 0 dimension dimension

def CompletenessGoal (L sigma gamma ell : ℝ) : Prop :=
  ∀ (grade inputDimension outputDimension : ℕ),
    IsComplete (Set.univ : Set
      (Coefficient L sigma gamma ell grade inputDimension outputDimension))

def DenseCoreGoal (L sigma gamma ell : ℝ) : Prop :=
  ∀ (grade inputDimension outputDimension : ℕ),
    DenseRange (coreInclusion L sigma gamma ell grade inputDimension outputDimension)

def NormFormulaGoal (L sigma gamma ell : ℝ) : Prop :=
  ∀ (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension),
    ‖coefficient‖ = ∑' cell : ℤ, ∑ index : DerivativeIndex grade,
      ‖weightedDerivative coefficient cell index‖

def LiteralDerivativeGoal (L sigma gamma ell : ℝ) : Prop :=
  ∀ (grade inputDimension outputDimension : ℕ)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    weightedDerivative coefficient cell index point =
      (coefficientScale L sigma gamma ell grade cell index point : ℂ) •
        coefficientDerivative coefficient cell index point

def ComposeDerivativeGoal (L sigma gamma ell : ℝ)
    (compose : CompositionOperation L sigma gamma ell) : Prop :=
  ∀ (grade inputDimension middleDimension outputDimension : ℕ)
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative (compose grade inputDimension middleDimension outputDimension outer inner)
        cell index point = formalCompositionDerivative outer inner cell index point

def BaseProductGoal (L sigma gamma ell : ℝ)
    (compose : CompositionOperation L sigma gamma ell) : Prop :=
  ∀ (inputDimension middleDimension outputDimension : ℕ)
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension),
    ‖compose 0 inputDimension middleDimension outputDimension outer inner‖ ≤
      ‖outer‖ * ‖inner‖

def GradedProductGoal (L sigma gamma ell : ℝ)
    (compose : CompositionOperation L sigma gamma ell) : Prop :=
  ∀ (grade inputDimension middleDimension outputDimension : ℕ)
    (outer : Coefficient L sigma gamma ell grade middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell grade inputDimension middleDimension),
    ‖compose grade inputDimension middleDimension outputDimension outer inner‖ ≤
      gradeProductConstant grade * ‖outer‖ * ‖inner‖

def FourierProductGoal (L sigma gamma ell : ℝ)
    (compose : CompositionOperation L sigma gamma ell) : Prop :=
  ∀ (inputDimension middleDimension outputDimension : ℕ)
    (outer : Coefficient L sigma gamma ell 0 middleDimension outputDimension)
    (inner : Coefficient L sigma gamma ell 0 inputDimension middleDimension)
    (angle : ℝ) (point : ClosedDisk),
    fourierEvaluation (compose 0 inputDimension middleDimension outputDimension outer inner)
        angle point =
      (fourierEvaluation outer angle point).comp (fourierEvaluation inner angle point)

def IdentityGoal (L sigma gamma ell : ℝ)
    (identity : IdentityOperation L sigma gamma ell) : Prop :=
  (∀ (dimension : ℕ), 0 < dimension → ‖identity dimension‖ = 1) ∧
    ∀ (dimension : ℕ) (angle : ℝ) (point : ClosedDisk),
      fourierEvaluation (identity dimension) angle point = ContinuousLinearMap.id ℂ _

/-- A witness contains the actual typed products and unit, while the carrier,
norm, dense core and evaluation are frozen above. -/
structure Construction (L sigma gamma ell : ℝ) where
  compose : CompositionOperation L sigma gamma ell
  identity : IdentityOperation L sigma gamma ell
  complete : CompletenessGoal L sigma gamma ell
  finiteCellCore_dense : DenseCoreGoal L sigma gamma ell
  norm_formula : NormFormulaGoal L sigma gamma ell
  weighted_derivative_literal : LiteralDerivativeGoal L sigma gamma ell
  compose_derivative : ComposeDerivativeGoal L sigma gamma ell compose
  base_product_norm : BaseProductGoal L sigma gamma ell compose
  graded_product_norm : GradedProductGoal L sigma gamma ell compose
  fourier_compose : FourierProductGoal L sigma gamma ell compose
  identity_goal : IdentityGoal L sigma gamma ell identity

def BlockGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell →
    Nonempty (Construction L sigma gamma ell)

end Grad.GaugeCoefficients.Algebra
