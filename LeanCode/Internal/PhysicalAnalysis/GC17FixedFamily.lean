import GC17InverseCoherence
import GC17LowMargin

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

def constantFamily (L sigma gamma ell : ℝ) {input output : ℕ} (value : OperatorValue input output) :
    CoefficientFamily L sigma gamma ell input output :=
  fun grade => seedConstantCell L sigma gamma ell grade 0 value

theorem constantFamily_coherent (L sigma gamma ell : ℝ) {input output : ℕ}
    (value : OperatorValue input output) : FamilyCoherent (constantFamily L sigma gamma ell value) := by
  intro grade other index otherIndex same cell point
  change coefficientDerivative (seedConstantCell L sigma gamma ell grade 0 value) cell index point =
    coefficientDerivative (seedConstantCell L sigma gamma ell other 0 value) cell otherIndex point
  rw [seedConstantCell_derivative, seedConstantCell_derivative]
  rw [show derivativeOrder index = derivativeOrder otherIndex from congrArg cartesianOrder same]

def fixedFamilyConstant {input output : ℕ} (value : OperatorValue input output) (grade : ℕ) : ℝ :=
  (Fintype.card (DerivativeIndex grade) : ℝ) * ‖value‖

theorem fixedFamilyConstant_nonnegative {input output : ℕ} (value : OperatorValue input output)
    (grade : ℕ) : 0 ≤ fixedFamilyConstant value grade := mul_nonneg (Nat.cast_nonneg _) (norm_nonneg value)

theorem constantFamily_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (value : OperatorValue input output) (grade : ℕ) :
    ‖constantFamily L sigma gamma ell value grade‖ ≤ fixedFamilyConstant value grade :=
  seedZeroCell_norm_le admissible value

theorem constantFamily_physicalValue {L sigma gamma ell : ℝ}
    (_admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (value : OperatorValue input output) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (constantFamily L sigma gamma ell value grade) angle point = value := by
  rw [coherent_physicalValue _ (constantFamily_coherent L sigma gamma ell value)]
  change fourierEvaluation (seedConstantCell L sigma gamma ell 0 0 value) angle point = value
  rw [seedConstantCell_fourier]
  simp [fourierPhase]

theorem family_physicalValue_comp {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input middle output : ℕ}
    (outer : CoefficientFamily L sigma gamma ell middle output)
    (inner : CoefficientFamily L sigma gamma ell input middle)
    (outerCoherent : FamilyCoherent outer) (innerCoherent : FamilyCoherent inner)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (coefficientComposition admissible grade (outer grade) (inner grade)) angle point =
      (coefficientPhysicalValue (outer grade) angle point).comp
        (coefficientPhysicalValue (inner grade) angle point) := by
  rw [coherent_physicalValue _ (outerCoherent.comp admissible innerCoherent),
    coherent_physicalValue outer outerCoherent, coherent_physicalValue inner innerCoherent]
  exact fourierComposition admissible (outer 0) (inner 0) angle point

theorem family_physicalValue_add {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (first second : CoefficientFamily L sigma gamma ell input output)
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (first grade + second grade) angle point =
      coefficientPhysicalValue (first grade) angle point + coefficientPhysicalValue (second grade) angle point := by
  rw [coherent_physicalValue _ (firstCoherent.add secondCoherent),
    coherent_physicalValue first firstCoherent, coherent_physicalValue second secondCoherent]
  exact (seedFourierCLM admissible input output angle point).map_add (first 0) (second 0)

theorem family_physicalValue_smul {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (scalar : ℂ) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (scalar • family grade) angle point =
      scalar • coefficientPhysicalValue (family grade) angle point := by
  rw [coherent_physicalValue _ (coherent.smul scalar), coherent_physicalValue family coherent]
  exact (seedFourierCLM admissible input output angle point).map_smul scalar (family 0)

theorem family_physicalValue_sub {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (first second : CoefficientFamily L sigma gamma ell input output)
    (firstCoherent : FamilyCoherent first) (secondCoherent : FamilyCoherent second)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (first grade - second grade) angle point =
      coefficientPhysicalValue (first grade) angle point - coefficientPhysicalValue (second grade) angle point := by
  rw [coherent_physicalValue _ (firstCoherent.sub secondCoherent),
    coherent_physicalValue first firstCoherent, coherent_physicalValue second secondCoherent]
  exact (seedFourierCLM admissible input output angle point).map_sub (first 0) (second 0)

theorem referenceFrame_apply (value : PhysicalValue 3) :
    referenceFrame value = WithLp.toLp 2 ![value 0, value 2, value 1] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [referenceFrame, columnEmbedding_apply]

theorem referenceFrame_norm_map (value : PhysicalValue 3) : ‖referenceFrame value‖ = ‖value‖ := by
  rw [referenceFrame_apply, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  simp only [Fin.sum_univ_three]
  change Real.sqrt (‖value 0‖ ^ 2 + ‖value 2‖ ^ 2 + ‖value 1‖ ^ 2) = _
  congr 1
  ring

theorem referenceFrame_norm_le : ‖referenceFrame‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro value
  rw [referenceFrame_norm_map, one_mul]

theorem referenceFrame_square : referenceFrame.comp referenceFrame = ContinuousLinearMap.id ℂ (PhysicalValue 3) := by
  apply ContinuousLinearMap.ext
  intro value
  change referenceFrame (referenceFrame value) = value
  rw [referenceFrame_apply, referenceFrame_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem constantFamily_base_norm_le {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ} (value : OperatorValue input output) :
    ‖constantFamily L sigma gamma ell value 0‖ ≤ ‖value‖ := by
  have bound := constantFamily_norm_le admissible value 0
  have card : Fintype.card (DerivativeIndex 0) = 1 := by
    exact Fintype.card_eq_one_iff.mpr ⟨zeroDerivativeIndex, fun index =>
      derivativeIndex_eq_zeroDerivativeIndexAt_of_order_zero index (Nat.eq_zero_of_le_zero index.2)⟩
  simpa only [fixedFamilyConstant, card, Nat.cast_one, one_mul] using bound

end Grad.GaugeCoefficients.Physical.Ledger
