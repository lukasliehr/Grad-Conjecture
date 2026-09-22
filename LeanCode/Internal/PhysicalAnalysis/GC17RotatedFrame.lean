import GC17PolynomialFamily
import GC17MatrixOperators

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def coordinateIdentityFamily (L sigma gamma ell : ℝ) (direction : Fin 2) :
    CoefficientFamily L sigma gamma ell 3 3 :=
  coordinateFamily L sigma gamma ell direction (ContinuousLinearMap.id ℂ (PhysicalValue 3))

theorem coordinateIdentityFamily_coherent (L sigma gamma ell : ℝ) (direction : Fin 2) :
    FamilyCoherent (coordinateIdentityFamily L sigma gamma ell direction) :=
  fixedJetFamily_coherent L sigma gamma ell _

def coordinateIdentityConstant (direction : Fin 2) (grade : ℕ) : ℝ :=
  fixedJetConstant (coordinateOperatorJet direction (ContinuousLinearMap.id ℂ (PhysicalValue 3))) grade

theorem coordinateIdentityConstant_nonnegative (direction : Fin 2) (grade : ℕ) :
    0 ≤ coordinateIdentityConstant direction grade := fixedJetConstant_nonnegative _ grade

theorem coordinateIdentityFamily_bound (L sigma gamma ell : ℝ) (direction : Fin 2) (grade : ℕ) :
    ‖coordinateIdentityFamily L sigma gamma ell direction grade‖ ≤ coordinateIdentityConstant direction grade :=
  fixedJetFamily_norm_le L sigma gamma ell _ grade

def frameFirstDerivative (parameters : PhaseParameters) (L ell epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  derivativeFamily (1, 0) (actualFrameFamily parameters L ell epsilon field)

def frameSecondDerivative (parameters : PhaseParameters) (L ell epsilon : ℝ) (field : ACore parameters 3) :
    CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  derivativeFamily (0, 1) (actualFrameFamily parameters L ell epsilon field)

def framePartialConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) * frameConstant parameters L (grade + 1)

theorem framePartialConstant_nonnegative (parameters : PhaseParameters) {L : ℝ}
    (positive : 0 < L) (grade : ℕ) : 0 ≤ framePartialConstant parameters L grade :=
  mul_nonneg (Nat.cast_nonneg _) (frameConstant_nonnegative parameters positive (grade + 1))

theorem framePartial_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3)
    (fixed : CartesianMultiIndex) (firstOrder : cartesianOrder fixed = 1) (grade : ℕ) :
    ‖derivativeFamily fixed (actualFrameFamily parameters L ell epsilon field) grade‖ ≤
      framePartialConstant parameters L grade * physicalBudget parameters field rho epsilon (5 + grade) := by
  apply (coefficientDerivativeShift_norm_le L parameters.sigma0 parameters.gamma ell grade 3 3 fixed _).trans
  have bound := mul_le_mul_of_nonneg_left
    (actualFrameFamily_bound parameters admissible epsilon rho epsilonSmall field (grade + cartesianOrder fixed))
    (Nat.cast_nonneg (Fintype.card (DerivativeIndex grade)) : (0 : ℝ) ≤ _)
  simpa only [firstOrder, framePartialConstant, mul_assoc,
    show 4 + (grade + 1) = 5 + grade by omega] using bound

/-- Literal rescaled angular vector field, including the axis. -/
def actualRotatedFrame {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3 :=
  fun grade => -coefficientComposition admissible grade
    (coordinateIdentityFamily L parameters.sigma0 parameters.gamma ell 1 grade)
    (frameFirstDerivative parameters L ell epsilon field grade) +
      coefficientComposition admissible grade
        (coordinateIdentityFamily L parameters.sigma0 parameters.gamma ell 0 grade)
        (frameSecondDerivative parameters L ell epsilon field grade)

theorem actualRotatedFrame_coherent {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) : FamilyCoherent (actualRotatedFrame parameters admissible epsilon field) := by
  have first := (coordinateIdentityFamily_coherent L parameters.sigma0 parameters.gamma ell 1).comp admissible
    (derivativeFamily_coherent (1, 0) _ (actualFrameFamily_coherent parameters admissible epsilon field))
  have second := (coordinateIdentityFamily_coherent L parameters.sigma0 parameters.gamma ell 0).comp admissible
    (derivativeFamily_coherent (0, 1) _ (actualFrameFamily_coherent parameters admissible epsilon field))
  unfold actualRotatedFrame frameFirstDerivative frameSecondDerivative
  simpa only [neg_one_smul] using (first.smul (-1 : ℂ)).add second

def rotatedFrameConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  (gradeProductConstant grade * coordinateIdentityConstant 1 grade +
    gradeProductConstant grade * coordinateIdentityConstant 0 grade) * framePartialConstant parameters L grade

theorem rotatedFrameConstant_nonnegative (parameters : PhaseParameters) {L : ℝ}
    (positive : 0 < L) (grade : ℕ) : 0 ≤ rotatedFrameConstant parameters L grade :=
  mul_nonneg (add_nonneg
    (mul_nonneg (gradeProductConstant_nonnegative grade) (coordinateIdentityConstant_nonnegative 1 grade))
    (mul_nonneg (gradeProductConstant_nonnegative grade) (coordinateIdentityConstant_nonnegative 0 grade)))
    (framePartialConstant_nonnegative parameters positive grade)

theorem actualRotatedFrame_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho epsilon : ℝ) (epsilonSmall : |epsilon| ≤ 1) (field : ACore parameters 3) (grade : ℕ) :
    ‖actualRotatedFrame parameters admissible epsilon field grade‖ ≤
      rotatedFrameConstant parameters L grade * physicalBudget parameters field rho epsilon (5 + grade) := by
  have each (direction : Fin 2) (fixed : CartesianMultiIndex) (firstOrder : cartesianOrder fixed = 1) :
      ‖coefficientComposition admissible grade
        (coordinateIdentityFamily L parameters.sigma0 parameters.gamma ell direction grade)
        (derivativeFamily fixed (actualFrameFamily parameters L ell epsilon field) grade)‖ ≤
        (gradeProductConstant grade * coordinateIdentityConstant direction grade) *
          (framePartialConstant parameters L grade * physicalBudget parameters field rho epsilon (5 + grade)) := by
    apply (coefficientComposition_norm_le admissible grade _ _).trans
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (coordinateIdentityFamily_bound L parameters.sigma0 parameters.gamma ell direction grade)
        (gradeProductConstant_nonnegative grade))
      (framePartial_bound parameters admissible rho epsilon epsilonSmall field fixed firstOrder grade)
      (norm_nonneg _) (mul_nonneg (gradeProductConstant_nonnegative grade)
        (coordinateIdentityConstant_nonnegative direction grade))
  change ‖-coefficientComposition admissible grade _ _ + coefficientComposition admissible grade _ _‖ ≤ _
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  exact (add_le_add (each 1 (1, 0) rfl) (each 0 (0, 1) rfl)).trans_eq (by
    unfold rotatedFrameConstant
    ring)

theorem frameFirstDerivative_physicalValue {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (frameFirstDerivative parameters L ell epsilon field grade) angle point =
      ∑' cell : ℤ, fourierPhase cell angle •
        coefficientDerivative (actualFrameFamily parameters L ell epsilon field 1) cell firstSpatialIndex point := by
  unfold coefficientPhysicalValue frameFirstDerivative derivativeFamily
  simp_rw [coefficientDerivativeShift_derivative]
  apply tsum_congr
  intro cell
  apply congrArg (fun value : OperatorValue 3 3 => fourierPhase cell angle • value)
  exact actualFrameFamily_coherent parameters admissible epsilon field (grade + 1) 1
    (raisedDerivativeIndex (1, 0) (Neumann.Regularity.zeroDerivativeIndexAt grade)) firstSpatialIndex rfl cell point

theorem frameSecondDerivative_physicalValue {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (frameSecondDerivative parameters L ell epsilon field grade) angle point =
      ∑' cell : ℤ, fourierPhase cell angle •
        coefficientDerivative (actualFrameFamily parameters L ell epsilon field 1) cell secondSpatialIndex point := by
  unfold coefficientPhysicalValue frameSecondDerivative derivativeFamily
  simp_rw [coefficientDerivativeShift_derivative]
  apply tsum_congr
  intro cell
  apply congrArg (fun value : OperatorValue 3 3 => fourierPhase cell angle • value)
  exact actualFrameFamily_coherent parameters admissible epsilon field (grade + 1) 1
    (raisedDerivativeIndex (0, 1) (Neumann.Regularity.zeroDerivativeIndexAt grade)) secondSpatialIndex rfl cell point

theorem actualRotatedFrame_physicalValue {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    operatorMatrix (coefficientPhysicalValue (actualRotatedFrame parameters admissible epsilon field grade) angle point) =
      rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point := by
  have firstCoherent : FamilyCoherent (frameFirstDerivative parameters L ell epsilon field) :=
    derivativeFamily_coherent (1, 0) _ (actualFrameFamily_coherent parameters admissible epsilon field)
  have secondCoherent : FamilyCoherent (frameSecondDerivative parameters L ell epsilon field) :=
    derivativeFamily_coherent (0, 1) _ (actualFrameFamily_coherent parameters admissible epsilon field)
  have firstProduct := (coordinateIdentityFamily_coherent L parameters.sigma0 parameters.gamma ell 1).comp
    admissible firstCoherent
  have secondProduct := (coordinateIdentityFamily_coherent L parameters.sigma0 parameters.gamma ell 0).comp
    admissible secondCoherent
  unfold actualRotatedFrame
  rw [show -coefficientComposition admissible grade _ _ =
    (-1 : ℂ) • coefficientComposition admissible grade
      (coordinateIdentityFamily L parameters.sigma0 parameters.gamma ell 1 grade)
      (frameFirstDerivative parameters L ell epsilon field grade) by rw [neg_one_smul]]
  rw [family_physicalValue_add admissible _ _ (firstProduct.smul (-1)) secondProduct,
    family_physicalValue_smul admissible _ firstProduct,
    family_physicalValue_comp admissible _ _
      (coordinateIdentityFamily_coherent L parameters.sigma0 parameters.gamma ell 1) firstCoherent,
    family_physicalValue_comp admissible _ _
      (coordinateIdentityFamily_coherent L parameters.sigma0 parameters.gamma ell 0) secondCoherent]
  unfold coordinateIdentityFamily
  rw [coordinateFamily_physicalValue, coordinateFamily_physicalValue,
    frameFirstDerivative_physicalValue parameters admissible, frameSecondDerivative_physicalValue parameters admissible]
  unfold rotatedPhysicalFrameMatrix
  congr 1
  apply ContinuousLinearMap.ext
  intro value
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  module

end Grad.GaugeCoefficients.Physical.Ledger
