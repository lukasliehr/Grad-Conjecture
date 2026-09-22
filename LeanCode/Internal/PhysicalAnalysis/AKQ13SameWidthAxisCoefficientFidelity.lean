import AKQ12SameWidthAxisCoefficientBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearDivision

local instance {sigma gamma : ℝ} {grade input output : ℕ} :
    CompleteSpace (Coefficient 1 sigma gamma 1 grade input output) := by
  unfold Coefficient
  infer_instance

theorem axisFrozenCoefficient_derivative {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {grade input output : ℕ} (coefficient : Coefficient 1 sigma gamma 1 grade input output)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (axisFrozenCoefficient coefficient) cell index point =
      if derivativeOrder index = 0 then
        coefficientDerivative coefficient cell (zeroDerivativeIndexAt grade) closedOrigin else 0 := by
  rw [axisFrozenCoefficient,seedDerivative_tsum _ (axisFrozenCell_norm_summable admissible coefficient).of_norm]
  simp_rw [axisFrozenCell,seedConstantCell_derivative]
  simp

def axisFrozenCoefficientLinear {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (grade input output : ℕ) :
    Coefficient 1 sigma gamma 1 grade input output →ₗ[ℂ] Coefficient 1 sigma gamma 1 grade input output where
  toFun := axisFrozenCoefficient
  map_add' first second := by
    apply coefficient_ext
    intro cell index point
    simp only [axisFrozenCoefficient_derivative admissible,coefficientDerivative_add_apply]
    split_ifs <;> simp
  map_smul' scalar coefficient := by
    change axisFrozenCoefficient (scalar • coefficient) = scalar • axisFrozenCoefficient coefficient
    apply coefficient_ext
    intro cell index point
    simp only [axisFrozenCoefficient_derivative admissible,coefficientDerivative_smul_apply]
    split_ifs
    · rfl
    · exact (smul_zero (M := ℂ) (A := OperatorValue input output) scalar).symm

def axisFrozenCoefficientMap {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (grade input output : ℕ) :
    Coefficient 1 sigma gamma 1 grade input output →L[ℂ] Coefficient 1 sigma gamma 1 grade input output :=
  (axisFrozenCoefficientLinear admissible grade input output).mkContinuous
    (Fintype.card (DerivativeIndex grade)) (axisFrozenCoefficient_norm_le admissible)

def axisFrozenFamily {sigma gamma : ℝ} {input output : ℕ}
    (family : CoefficientFamily 1 sigma gamma 1 input output) : CoefficientFamily 1 sigma gamma 1 input output :=
  fun grade => axisFrozenCoefficient (family grade)

theorem axisFrozenFamily_coherent {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {input output : ℕ} (family : CoefficientFamily 1 sigma gamma 1 input output)
    (coherent : FamilyCoherent family) : FamilyCoherent (axisFrozenFamily family) := by
  intro grade other index otherIndex same cell point
  have sameOrder : derivativeOrder index = derivativeOrder otherIndex := congrArg cartesianOrder same
  change coefficientDerivative (axisFrozenCoefficient (family grade)) cell index point =
    coefficientDerivative (axisFrozenCoefficient (family other)) cell otherIndex point
  rw [axisFrozenCoefficient_derivative admissible,axisFrozenCoefficient_derivative admissible,← sameOrder]
  split_ifs
  · exact coherent grade other (zeroDerivativeIndexAt grade) (zeroDerivativeIndexAt other) rfl cell closedOrigin
  · rfl

/-- Every physical Fourier value is the value at the original axis,
including cell zero. The new field is constant only in the disk variable. -/
theorem axisFrozenCoefficient_physicalValue {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {grade input output : ℕ} (coefficient : Coefficient 1 sigma gamma 1 grade input output)
    (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (axisFrozenCoefficient coefficient) angle point =
      coefficientPhysicalValue coefficient angle closedOrigin := by
  apply tsum_congr
  intro cell
  simp only [axisFrozenCoefficient_derivative admissible,derivativeOrder_zeroDerivativeIndexAt,if_true]

/-- Same one-high majorant, now for the actual circle coefficient at the
unchanged original width. The base map is a contraction by AKQ12. -/
theorem axisFrozenFamily_bound {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    {input output : ℕ} (family : CoefficientFamily 1 sigma gamma 1 input output)
    (bound : ℕ → ℝ) (estimate : ∀ grade, ‖family grade‖ ≤ bound grade) (grade : ℕ) :
    ‖axisFrozenFamily family grade‖ ≤ Fintype.card (DerivativeIndex grade) * bound grade :=
  (axisFrozenCoefficient_norm_le admissible (family grade)).trans
    (mul_le_mul_of_nonneg_left (estimate grade) (Nat.cast_nonneg _))

end Grad.FinitePhysicalJetLift
