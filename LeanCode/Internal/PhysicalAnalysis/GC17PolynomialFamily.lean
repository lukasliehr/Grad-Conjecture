import GC17DerivativeShift

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def fixedJetFamily (L sigma gamma ell : ℝ) {input output : ℕ} (jet : SmoothOperatorJet input output) :
    CoefficientFamily L sigma gamma ell input output :=
  fun grade => familyCell L sigma gamma ell grade (fun _ => jet) 0

theorem fixedJetFamily_derivative (L sigma gamma ell : ℝ) {input output : ℕ}
    (jet : SmoothOperatorJet input output) (grade : ℕ) (cell : ℤ) (index : DerivativeIndex grade)
    (point : ClosedDisk) :
    coefficientDerivative (fixedJetFamily L sigma gamma ell jet grade) cell index point =
      if cell = 0 then smoothOperatorDerivative jet (derivativeMultiIndex index) point else 0 := by
  change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
    weightedSingle L sigma gamma ell grade 0 jet (cell, index) point = _
  rw [weightedSingle_apply]
  by_cases zeroCell : cell = 0
  · subst cell
    rw [if_pos rfl]
    change ((coefficientScale L sigma gamma ell grade 0 index point : ℂ)⁻¹) •
        ((coefficientScale L sigma gamma ell grade 0 index point : ℂ) •
          smoothOperatorDerivative jet (derivativeMultiIndex index) point) = _
    rw [← mul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (coefficientScale_pos L sigma gamma ell grade 0 index point).ne'), one_smul, if_pos rfl]
  · rw [if_neg zeroCell, if_neg zeroCell]
    change ((coefficientScale L sigma gamma ell grade cell index point : ℂ)⁻¹) •
      (0 : OperatorValue input output) = 0
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

theorem fixedJetFamily_coherent (L sigma gamma ell : ℝ) {input output : ℕ}
    (jet : SmoothOperatorJet input output) : FamilyCoherent (fixedJetFamily L sigma gamma ell jet) := by
  intro grade other index otherIndex same cell point
  rw [fixedJetFamily_derivative, fixedJetFamily_derivative, same]

def fixedJetConstant {input output : ℕ} (jet : SmoothOperatorJet input output) (grade : ℕ) : ℝ :=
  ∑ index : DerivativeIndex grade, ‖smoothOperatorDerivative jet (derivativeMultiIndex index)‖

theorem fixedJetConstant_nonnegative {input output : ℕ} (jet : SmoothOperatorJet input output)
    (grade : ℕ) : 0 ≤ fixedJetConstant jet grade :=
  Finset.sum_nonneg fun index _ => norm_nonneg (smoothOperatorDerivative jet (derivativeMultiIndex index))

theorem fixedJetFamily_norm_le (L sigma gamma ell : ℝ) {input output : ℕ}
    (jet : SmoothOperatorJet input output) (grade : ℕ) :
    ‖fixedJetFamily L sigma gamma ell jet grade‖ ≤ fixedJetConstant jet grade := by
  apply (familyCell_norm_le L sigma gamma ell grade (fun _ => jet) 0).trans_eq
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  apply ContinuousMap.ext
  intro point
  change (coefficientScale L sigma gamma ell grade 0 index point : ℂ) •
    smoothOperatorDerivative jet (derivativeMultiIndex index) point = _
  have scaleOne : coefficientScale L sigma gamma ell grade 0 index point = 1 := by
    simp [coefficientScale, originalEnvelope, scaledCellWeight]
  rw [scaleOne, Complex.ofReal_one, one_smul]

theorem fixedJetFamily_physicalValue (L sigma gamma ell : ℝ) {input output : ℕ}
    (jet : SmoothOperatorJet input output) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (fixedJetFamily L sigma gamma ell jet grade) angle point = jet.value point := by
  unfold coefficientPhysicalValue
  simp_rw [fixedJetFamily_derivative]
  rw [tsum_eq_single 0]
  · simp only [ite_true]
    have zeroDerivative : smoothOperatorDerivative jet (0, 0) = jet.value := by
      apply smoothOperatorDerivative_eq_of_spec
      intro candidate inside
      change jet.value candidate = closedDiskLift jet.value candidate.val
      unfold closedDiskLift
      rw [dif_pos (openDiskMembershipClosed candidate.val inside)]
    change fourierPhase 0 angle • smoothOperatorDerivative jet (0, 0) point = _
    rw [zeroDerivative]
    simp [fourierPhase]
  · intro cell different
    rw [if_neg different]
    apply ContinuousLinearMap.ext
    intro value
    simp only [smul_apply, zero_apply, smul_zero]

def coordinateOperatorMap {input output : ℕ} (direction : Fin 2) (value : OperatorValue input output) :
    ComplexEuclidean 3 →L[ℂ] OperatorValue input output :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℂ) (if direction = 0 then 0 else 2)).smulRight value

def coordinateOperatorJet {input output : ℕ} (direction : Fin 2) (value : OperatorValue input output) :
    SmoothOperatorJet input output :=
  mappedSmoothOperatorJet (coordinateOperatorMap direction value) referenceStateJet

theorem coordinateOperatorJet_value {input output : ℕ} (direction : Fin 2)
    (value : OperatorValue input output) (point : ClosedDisk) :
    (coordinateOperatorJet direction value).value point = (point.val direction : ℂ) • value := by
  change referenceStateValue point (if direction = 0 then 0 else 2) • value = _
  fin_cases direction <;> rfl

def coordinateFamily (L sigma gamma ell : ℝ) {input output : ℕ}
    (direction : Fin 2) (value : OperatorValue input output) : CoefficientFamily L sigma gamma ell input output :=
  fixedJetFamily L sigma gamma ell (coordinateOperatorJet direction value)

theorem coordinateFamily_physicalValue (L sigma gamma ell : ℝ) {input output : ℕ}
    (direction : Fin 2) (value : OperatorValue input output) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (coordinateFamily L sigma gamma ell direction value grade) angle point =
      (point.val direction : ℂ) • value :=
  (fixedJetFamily_physicalValue L sigma gamma ell _ grade angle point).trans
    (coordinateOperatorJet_value direction value point)

end Grad.GaugeCoefficients.Physical.Ledger
