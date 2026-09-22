import GC10Proof
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import SP1Consumers

noncomputable section

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 5000000

open Set MeasureTheory
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators Interval Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra
open Grad.RepresentedKernel.SpatialProduct
open Grad.WeakTesting.Commutation

/-- The continuous clamp used only to totalize radial formulas outside the
integration interval.  On `[0,1]` it is literally the identity. -/
def unitClamp (time : ℝ) : ℝ := max 0 (min 1 time)

theorem unitClamp_nonnegative (time : ℝ) : 0 ≤ unitClamp time := by
  exact le_max_left _ _

theorem unitClamp_le_one (time : ℝ) : unitClamp time ≤ 1 := by
  unfold unitClamp
  exact max_le zero_le_one (min_le_left _ _)

theorem unitClamp_of_mem {time : ℝ} (membership : time ∈ Icc (0 : ℝ) 1) :
    unitClamp time = time := by
  simp [unitClamp, membership.1, membership.2]

/-- Radial contraction of the closed disk. -/
def radialPoint (time : ℝ) (point : ClosedDisk) : ClosedDisk :=
  ⟨unitClamp time • point.val, by
    change ‖unitClamp time • point.val‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (unitClamp_nonnegative time)]
    exact (mul_le_of_le_one_left (norm_nonneg point.val)
      (unitClamp_le_one time)).trans point.property⟩

/-- Counterclockwise planar rotation in the literal two Cartesian variables. -/
def planeRotation (angle : ℝ) (point : SpatialPlane) : SpatialPlane :=
  WithLp.toLp 2 ![
    Real.cos angle * point 0 - Real.sin angle * point 1,
    Real.sin angle * point 0 + Real.cos angle * point 1]

theorem planeRotation_norm (angle : ℝ) (point : SpatialPlane) :
    ‖planeRotation angle point‖ = ‖point‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_two]
  change Real.sqrt (‖Real.cos angle * point 0 - Real.sin angle * point 1‖ ^ 2 +
      ‖Real.sin angle * point 0 + Real.cos angle * point 1‖ ^ 2) =
    Real.sqrt (‖point 0‖ ^ 2 + ‖point 1‖ ^ 2)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq angle]

def rotatedPoint (angle : ℝ) (point : ClosedDisk) : ClosedDisk :=
  ⟨planeRotation angle point.val, by
    change ‖planeRotation angle point.val‖ ≤ 1
    rw [planeRotation_norm]
    exact point.property⟩

/-- A fixed genuine reflection, interchanging the two Cartesian axes. -/
def planeReflection (point : SpatialPlane) : SpatialPlane :=
  WithLp.toLp 2 ![point 1, point 0]

theorem planeReflection_norm (point : SpatialPlane) :
    ‖planeReflection point‖ = ‖point‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_two]
  change Real.sqrt (‖point 1‖ ^ 2 + ‖point 0‖ ^ 2) =
    Real.sqrt (‖point 0‖ ^ 2 + ‖point 1‖ ^ 2)
  rw [add_comm]

def planeReflectionEquiv : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane where
  toFun := planeReflection
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> rfl
  map_smul' scalar point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> rfl
  norm_map' := planeReflection_norm
  invFun := planeReflection
  left_inv point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> rfl
  right_inv point := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> rfl

def reflectedPoint (point : ClosedDisk) : ClosedDisk :=
  ⟨planeReflection point.val, by
    change ‖planeReflection point.val‖ ≤ 1
    rw [planeReflection_norm]
    exact point.property⟩

def zeroDerivativeIndexAt (grade : ℕ) : DerivativeIndex grade :=
  ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), by simp⟩

def orthogonalDerivativeIndex {grade : ℕ} (index : DerivativeIndex grade)
    (target : Word (derivativeOrder index)) : DerivativeIndex grade := by
  have total := count_total (derivativeOrder index) target
  have orderLe : derivativeOrder index ≤ grade := index.2
  refine ⟨(⟨directionCount target 0, ?_⟩,
    ⟨directionCount target 1, ?_⟩), ?_⟩
  · omega
  · omega
  · change directionCount target 0 + directionCount target 1 ≤ grade
    omega

def derivativeWord {grade : ℕ} (index : DerivativeIndex grade) :
    Word (derivativeOrder index) :=
  cartesianMultiIndexWord (derivativeMultiIndex index)

/-- Add two derivatives in the first Cartesian direction. -/
def firstLaplacianIndex {grade : ℕ} (index : DerivativeIndex grade) :
    DerivativeIndex (grade + 2) := by
  refine ⟨(⟨(index.1.1 : ℕ) + 2, ?_⟩,
    ⟨(index.1.2 : ℕ), ?_⟩), ?_⟩
  · have := index.2
    omega
  · have := index.2
    omega
  · change (index.1.1 : ℕ) + 2 + (index.1.2 : ℕ) ≤ grade + 2
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      Nat.add_le_add_right index.2 2

/-- Add two derivatives in the second Cartesian direction. -/
def secondLaplacianIndex {grade : ℕ} (index : DerivativeIndex grade) :
    DerivativeIndex (grade + 2) := by
  refine ⟨(⟨(index.1.1 : ℕ), ?_⟩,
    ⟨(index.1.2 : ℕ) + 2, ?_⟩), ?_⟩
  · have := index.2
    omega
  · have := index.2
    omega
  · change (index.1.1 : ℕ) + ((index.1.2 : ℕ) + 2) ≤ grade + 2
    simpa [Nat.add_assoc] using Nat.add_le_add_right index.2 2

/-- Literal AP16 formula, written on the unweighted closed derivative. -/
def radialIntegralDerivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    OperatorValue inputDimension outputDimension :=
  ∫ time in Icc (0 : ℝ) 1,
    (Real.negMulLog time : ℂ) •
      ((time ^ derivativeOrder index : ℝ) : ℂ) •
        coefficientDerivative coefficient cell index (radialPoint time point)

/-- Literal Cartesian Laplacian on the coefficient closed jet. -/
def laplacianDerivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    OperatorValue inputDimension outputDimension :=
  coefficientDerivative coefficient cell (firstLaplacianIndex index) point +
    coefficientDerivative coefficient cell (secondLaplacianIndex index) point

def reflectionDerivative {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    OperatorValue inputDimension outputDimension :=
  ∑ target : Word (derivativeOrder index),
    (chainFactor (derivativeOrder index) planeReflectionEquiv
      (derivativeWord index) target : ℂ) •
      coefficientDerivative coefficient cell
        (orthogonalDerivativeIndex index target) (reflectedPoint point)

/-- Normalized angular average, parameterized by one turn of `[0,1]`. -/
def angularMeanValue {L sigma gamma ell : ℝ}
    {grade inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (point : ClosedDisk) : OperatorValue inputDimension outputDimension :=
  ∫ time in Icc (0 : ℝ) 1,
    coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade)
      (rotatedPoint (2 * Real.pi * time) point)

def angularBound (grade : ℕ) : ℝ :=
  Fintype.card (DerivativeIndex grade) * 2 ^ grade

def reflectionBound (grade : ℕ) : ℝ := angularBound grade

/-- A deliberately transparent finite-grade constant for the two Cartesian
second derivatives. -/
def laplacianBound (grade : ℕ) : ℝ :=
  2 * Fintype.card (DerivativeIndex grade)

abbrev RadialIntegralOperation (L sigma gamma ell : ℝ) :=
  ∀ (grade inputDimension outputDimension : ℕ),
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension

abbrev LaplacianOperation (L sigma gamma ell : ℝ) :=
  ∀ (grade inputDimension outputDimension : ℕ),
    Coefficient L sigma gamma ell (grade + 2) inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension

abbrev ReflectionOperation (L sigma gamma ell : ℝ) :=
  ∀ (grade inputDimension outputDimension : ℕ),
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension

abbrev AngularMeanOperation (L sigma gamma ell : ℝ) :=
  ∀ (grade inputDimension outputDimension : ℕ),
    Coefficient L sigma gamma ell grade inputDimension outputDimension →L[ℂ]
      Coefficient L sigma gamma ell grade inputDimension outputDimension

/-- The cell-zero coefficient of any fixed smooth closed-disk multiplier.
Cartesian polynomials are the special case used in AP5. -/
def fixedCoefficient (L sigma gamma ell : ℝ) (grade : ℕ)
    {middleDimension outputDimension : ℕ}
    (field : SmoothOperatorJet middleDimension outputDimension) :
    Coefficient L sigma gamma ell grade middleDimension outputDimension :=
  coreInclusion L sigma gamma ell grade middleDimension outputDimension
    ⟨weightedSingle L sigma gamma ell grade 0 field,
      Submodule.subset_span (Set.mem_range.mpr ⟨(0, field), rfl⟩)⟩

abbrev FixedMultiplierOperation (L sigma gamma ell : ℝ) :=
  ∀ (grade inputDimension middleDimension outputDimension : ℕ),
    SmoothOperatorJet middleDimension outputDimension →
      Coefficient L sigma gamma ell grade inputDimension middleDimension →L[ℂ]
        Coefficient L sigma gamma ell grade inputDimension outputDimension

/-- Exact CT_GC13/AP16--AP17 contract on the frozen original-width
coefficient carrier. -/
structure Construction (L sigma gamma ell : ℝ) where
  admissible : Admissible L sigma gamma ell
  radialIntegral : RadialIntegralOperation L sigma gamma ell
  radialIntegral_bound : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension),
    ‖radialIntegral grade inputDimension outputDimension coefficient‖ ≤
      (1 : ℝ) / 4 * ‖coefficient‖
  radialIntegral_derivative : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative
        (radialIntegral grade inputDimension outputDimension coefficient) cell index point =
      radialIntegralDerivative coefficient cell index point
  laplacian : LaplacianOperation L sigma gamma ell
  laplacian_bound : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension),
    ‖laplacian grade inputDimension outputDimension coefficient‖ ≤
      laplacianBound grade * ‖coefficient‖
  laplacian_derivative : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell (grade + 2)
      inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative
        (laplacian grade inputDimension outputDimension coefficient) cell index point =
      laplacianDerivative coefficient cell index point
  reflection : ReflectionOperation L sigma gamma ell
  reflection_bound : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension),
    ‖reflection grade inputDimension outputDimension coefficient‖ ≤
      reflectionBound grade * ‖coefficient‖
  reflection_derivative : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative
        (reflection grade inputDimension outputDimension coefficient) cell index point =
      reflectionDerivative coefficient cell index point
  angularMean : AngularMeanOperation L sigma gamma ell
  angularMean_bound : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension),
    ‖angularMean grade inputDimension outputDimension coefficient‖ ≤
      angularBound grade * ‖coefficient‖
  angularMean_value : ∀ grade inputDimension outputDimension
    (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension)
    (cell : ℤ) (point : ClosedDisk),
    coefficientDerivative
        (angularMean grade inputDimension outputDimension coefficient)
        cell (zeroDerivativeIndexAt grade) point =
      angularMeanValue coefficient cell point
  fixedMultiplier : FixedMultiplierOperation L sigma gamma ell
  fixedMultiplier_bound : ∀ grade inputDimension middleDimension outputDimension
    (field : SmoothOperatorJet middleDimension outputDimension)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension middleDimension),
    ‖fixedMultiplier grade inputDimension middleDimension outputDimension field coefficient‖ ≤
      gradeProductConstant grade * ‖fixedCoefficient L sigma gamma ell grade field‖ *
        ‖coefficient‖
  fixedMultiplier_derivative : ∀ grade inputDimension middleDimension outputDimension
    (field : SmoothOperatorJet middleDimension outputDimension)
    (coefficient : Coefficient L sigma gamma ell grade inputDimension middleDimension)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk),
    coefficientDerivative
        (fixedMultiplier grade inputDimension middleDimension outputDimension field coefficient)
        cell index point =
      formalCompositionDerivative (fixedCoefficient L sigma gamma ell grade field)
        coefficient cell index point

def BlockGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell →
    Nonempty (Construction L sigma gamma ell)

end Grad.GaugeCoefficients.Radial
