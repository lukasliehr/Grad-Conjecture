import AKAG8CompactFirstToWholePlaneH1

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- One constant, independent of the physical scale and the input/output
 dimensions, controls both actual zeroth and genuine first weak graphs. -/
def startupFirstUniformConstant (L sigma gamma : ℝ) : ℝ :=
  3 * startupDerivativeConstant L sigma gamma zeroDerivativeIndex +
    startupDerivativeConstant L sigma gamma (startupFirstCoefficientIndex 0) +
    startupDerivativeConstant L sigma gamma (startupFirstCoefficientIndex 1)

variable {L sigma gamma ell : ℝ}

theorem startupFirstUniformConstant_nonnegative (admissible : Admissible L sigma gamma ell) :
    0 ≤ startupFirstUniformConstant L sigma gamma := by
  unfold startupFirstUniformConstant
  positivity [startupDerivativeConstant_nonnegative admissible zeroDerivativeIndex,
    startupDerivativeConstant_nonnegative admissible (startupFirstCoefficientIndex 0),
    startupDerivativeConstant_nonnegative admissible (startupFirstCoefficientIndex 1)]

theorem startupMatrix_uniform_bound (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent family) {zeroth first : ℝ}
    (zeroBound : ‖family 0‖ ≤ zeroth) (oneBound : ‖family 1‖ ≤ first) :
    ‖originalMatrixKernel admissible family coherent‖ ≤
        startupFirstUniformConstant L sigma gamma * (zeroth + first) ∧
    ‖startupMatrixFirstGraphCLM admissible family coherent‖ ≤
        startupFirstUniformConstant L sigma gamma * (zeroth + first) := by
  have c0 := startupDerivativeConstant_nonnegative admissible zeroDerivativeIndex
  have c1 := startupDerivativeConstant_nonnegative admissible (startupFirstCoefficientIndex 0)
  have c2 := startupDerivativeConstant_nonnegative admissible (startupFirstCoefficientIndex 1)
  have z := (norm_nonneg (family 0)).trans zeroBound
  have o := (norm_nonneg (family 1)).trans oneBound
  constructor
  · apply (originalMatrixKernel_bound admissible family coherent).trans
    have := mul_le_mul_of_nonneg_left zeroBound c0
    unfold startupFirstUniformConstant
    nlinarith [mul_nonneg c0 o, mul_nonneg c1 z, mul_nonneg c1 o,
      mul_nonneg c2 z, mul_nonneg c2 o, mul_nonneg c0 z]
  · apply (startupMatrixFirstGraphCLM_norm admissible family coherent).trans
    unfold startupMatrixFirstBudget startupFirstUniformConstant
    have h0 := mul_le_mul_of_nonneg_left zeroBound c0
    have h1 := mul_le_mul_of_nonneg_left oneBound c1
    have h2 := mul_le_mul_of_nonneg_left oneBound c2
    nlinarith [mul_nonneg c0 o, mul_nonneg c1 z, mul_nonneg c2 z]

/-- The completed full gauge has its literal identity term and no inverse
 scale cost. The two derivative-grade constants are fixed before ell. -/
theorem startupFullGauge_coefficient_bound (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (grade : ℕ) {bound : ℝ} (bounded : ‖gauge grade‖ ≤ bound) :
    ‖fullGaugeFamily gauge grade‖ ≤ (Fintype.card (DerivativeIndex grade) : ℝ) + bound := by
  exact (norm_add_le _ _).trans
    (add_le_add (identityFamily_norm_le L sigma gamma ell 3 grade) bounded)

/-- The SAME actual complement extension is bounded using its already
 proved determinant inverse estimate, retaining the original B6 domain. -/
theorem startupExtension_coefficient_bound {parameters : PhaseParameters}
    {L ell rho epsilon : ℝ} (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (base : ACore parameters 3)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ)
    (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters base rho epsilon 6 ≤ 1)
    (bounds : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters base rho epsilon (grade + 4))
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius constants)
    (grade : ℕ) :
    ‖complementExtensionFamily admissible gauge grade‖ ≤
      (Fintype.card (DerivativeIndex grade) : ℝ) +
      complementExtensionConstant constants grade * physicalBudget parameters base rho epsilon (grade + 6) := by
  have deviation := complementExtension_deviation_bound parameters admissible base rho epsilon gauge coherent
    constants nonnegative low bounds small grade
  have triangle := norm_add_le
    (complementExtensionFamily admissible gauge grade - identityFamily L parameters.sigma0 parameters.gamma ell 3 grade)
    (identityFamily L parameters.sigma0 parameters.gamma ell 3 grade)
  rw [sub_add_cancel] at triangle
  exact triangle.trans ((add_le_add deviation
    (identityFamily_norm_le L parameters.sigma0 parameters.gamma ell 3 grade)).trans_eq (add_comm _ _))

end Grad.CartesianStartup
