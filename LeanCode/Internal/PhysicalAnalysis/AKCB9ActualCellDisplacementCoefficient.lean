import AKCB8CoefficientCellReserve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

def startupAxialFrequency (L ell : ℝ) (cell : ℤ) : ℂ :=
  (((cell:ℝ)*ell/L : ℝ):ℂ)*Complex.I

theorem startupAxialFrequency_norm (L ell : ℝ) (cell : ℤ) :
    ‖startupAxialFrequency L ell cell‖≤scaledCellWeight L ell cell := by
  rw [startupAxialFrequency,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]
  unfold scaledCellWeight
  have square := Real.sq_sqrt (show 0≤1+((cell:ℝ)*ell/L)^2 by positivity)
  have positive := Real.sqrt_nonneg (1+((cell:ℝ)*ell/L)^2)
  nlinarith [sq_abs ((cell:ℝ)*ell/L)]

theorem startupAxialFrequency_sub (L ell : ℝ) (output input : ℤ) :
    startupAxialFrequency L ell (output-input)=
      startupAxialFrequency L ell output-startupAxialFrequency L ell input := by
  simp only [startupAxialFrequency,Int.cast_sub,sub_mul,sub_div,Complex.ofReal_sub]

/-- Literal p-th cell-displacement coefficient, with the original input reserve. -/
def startupDisplacementCoefficient {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) (input shift : ℤ) :
    C(ClosedDisk,OperatorValue inputDimension outputDimension) :=
  startupAxialFrequency L ell shift^power • startupDerivativeCoefficient admissible family coherent index input shift

theorem startupDisplacementCoefficient_bound {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (power : ℕ) (input shift : ℤ) :
    ‖startupDisplacementCoefficient admissible family coherent index power input shift‖≤
      startupDerivativeMajorant (family (grade+power)) (startupCellReserveIndex power index) shift := by
  unfold startupDisplacementCoefficient
  apply (startupCoefficientMap_smul_norm_le _ _).trans
  rw [norm_pow,startupDerivativeMajorant_cellReserve family coherent]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (startupAxialFrequency_norm L ell shift) power)
    (startupDerivativeCoefficient_bound admissible family coherent index input shift)
    (norm_nonneg (startupDerivativeCoefficient admissible family coherent index input shift))
    (pow_nonneg (scaledCellWeight_nonnegative L ell shift) _)

end Grad.CartesianStartup
