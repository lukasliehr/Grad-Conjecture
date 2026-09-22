import AKAA23ActualFirstGraphAssembly

noncomputable section

set_option maxHeartbeats 1800000

open MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.Ordered
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

variable {L sigma gamma ell : ℝ} {inputDimension outputDimension : ℕ}

def startupMatrixFirstGraph (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    GraphGrade outputDimension 1 0 openUnitDisk :=
  startupFirstGraph
    (startupDerivativeKernel admissible family coherent zeroDerivativeIndex
      (base inputDimension 1 openUnitDisk (fun _ => 0) field))
    (fun direction => startupDerivativeKernel admissible family coherent zeroDerivativeIndex
      (orderedDerivative inputDimension 1 1 openUnitDisk (fun _ => 0) le_rfl field (startupFirstWord direction)) +
      startupDerivativeKernel admissible family coherent (startupFirstCoefficientIndex direction)
        (base inputDimension 1 openUnitDisk (fun _ => 0) field))
    (fun direction => startupActualMatrix_firstWeak admissible family coherent direction le_rfl field)

theorem startupMatrixFirstGraph_base (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    base outputDimension 1 openUnitDisk (fun _ => 0) (startupMatrixFirstGraph admissible family coherent field) =
      originalMatrixKernel admissible family coherent (base inputDimension 1 openUnitDisk (fun _ => 0) field) :=
  startupFirstGraph_base _ _ _

def startupMatrixFirstBudget (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension) : ℝ :=
  startupDerivativeConstant L sigma gamma zeroDerivativeIndex * ‖family 0‖ +
    (startupDerivativeConstant L sigma gamma zeroDerivativeIndex * ‖family 0‖ +
      startupDerivativeConstant L sigma gamma (startupFirstCoefficientIndex 0) * ‖family 1‖) +
    (startupDerivativeConstant L sigma gamma zeroDerivativeIndex * ‖family 0‖ +
      startupDerivativeConstant L sigma gamma (startupFirstCoefficientIndex 1) * ‖family 1‖)

theorem startupMatrixFirstBudget_nonnegative (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension) :
    0 ≤ startupMatrixFirstBudget family := by
  have zeroth := mul_nonneg (startupDerivativeConstant_nonnegative admissible zeroDerivativeIndex) (norm_nonneg (family 0))
  have first (direction : Fin 2) := mul_nonneg
    (startupDerivativeConstant_nonnegative admissible (startupFirstCoefficientIndex direction)) (norm_nonneg (family 1))
  exact add_nonneg (add_nonneg zeroth (add_nonneg zeroth (first 0))) (add_nonneg zeroth (first 1))

theorem startupFirstInput_norm {dimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (field : GraphGrade dimension 1 0 domain) (direction : Fin 2) :
    ‖orderedDerivative dimension 1 1 domain (fun _ => 0) le_rfl field (startupFirstWord direction)‖ ≤ ‖field‖ := by
  have total := orderedDerivative_norm_le dimension 1 1 domain (fun _ => 0) le_rfl field
  norm_num only [Nat.factorial_one, Nat.cast_one, Real.sqrt_one, one_mul] at total
  exact (PiLp.norm_apply_le _ (startupFirstWord direction)).trans total

theorem startupKernel_input_bound (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) {grade : ℕ} (index : DerivativeIndex grade)
    (field : StartupL2 inputDimension) (bound : ℝ) (bounded : ‖field‖ ≤ bound) :
    ‖startupDerivativeKernel admissible family coherent index field‖ ≤
      (startupDerivativeConstant L sigma gamma index * ‖family grade‖) * bound := by
  exact ((startupDerivativeKernel admissible family coherent index).le_opNorm field).trans
    ((mul_le_mul_of_nonneg_right (startupDerivativeKernel_norm admissible family coherent index) (norm_nonneg field)).trans
      (mul_le_mul_of_nonneg_left bounded (mul_nonneg
        (startupDerivativeConstant_nonnegative admissible index) (norm_nonneg (family grade)))))

theorem startupMatrixFirstGraph_bound (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (field : GraphGrade inputDimension 1 0 openUnitDisk) :
    ‖startupMatrixFirstGraph admissible family coherent field‖ ≤ startupMatrixFirstBudget family * ‖field‖ := by
  let source := base inputDimension 1 openUnitDisk (fun _ => 0) field
  let derivative (direction : Fin 2) := orderedDerivative inputDimension 1 1 openUnitDisk (fun _ => 0) le_rfl field (startupFirstWord direction)
  have zeroth := startupKernel_input_bound admissible family coherent zeroDerivativeIndex source ‖field‖
    (base_norm_le inputDimension 1 openUnitDisk (fun _ => 0) field)
  have first (direction : Fin 2) :
      ‖startupDerivativeKernel admissible family coherent zeroDerivativeIndex (derivative direction) +
        startupDerivativeKernel admissible family coherent (startupFirstCoefficientIndex direction) source‖ ≤
      (startupDerivativeConstant L sigma gamma zeroDerivativeIndex * ‖family 0‖ +
        startupDerivativeConstant L sigma gamma (startupFirstCoefficientIndex direction) * ‖family 1‖) * ‖field‖ := by
    exact (norm_add_le _ _).trans ((add_le_add
      (startupKernel_input_bound admissible family coherent zeroDerivativeIndex (derivative direction) ‖field‖
        (startupFirstInput_norm field direction))
      (startupKernel_input_bound admissible family coherent (startupFirstCoefficientIndex direction) source ‖field‖
        (base_norm_le inputDimension 1 openUnitDisk (fun _ => 0) field))).trans_eq (add_mul _ _ _).symm)
  have graphBound := startupFirstGraph_norm_bound
    (startupDerivativeKernel admissible family coherent zeroDerivativeIndex source)
    (fun direction => startupDerivativeKernel admissible family coherent zeroDerivativeIndex (derivative direction) +
      startupDerivativeKernel admissible family coherent (startupFirstCoefficientIndex direction) source)
    (fun direction => startupActualMatrix_firstWeak admissible family coherent direction le_rfl field)
  exact graphBound.trans ((add_le_add (add_le_add zeroth (first 0)) (first 1)).trans_eq (by
    unfold startupMatrixFirstBudget
    ring))

/-- Bounded map on the existing genuine first weak graph, compatible with
 the exact complete-cell L2 multiplier. -/
def startupMatrixFirstGraphCLM (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) :
    GraphGrade inputDimension 1 0 openUnitDisk →L[ℂ] GraphGrade outputDimension 1 0 openUnitDisk := by
  let mapping : GraphGrade inputDimension 1 0 openUnitDisk →ₗ[ℂ] GraphGrade outputDimension 1 0 openUnitDisk := {
    toFun := startupMatrixFirstGraph admissible family coherent
    map_add' := by
      intro first second
      apply base_injective outputDimension 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
      rw [map_add, startupMatrixFirstGraph_base, startupMatrixFirstGraph_base, startupMatrixFirstGraph_base, map_add, map_add]
    map_smul' := by
      intro scalar field
      apply base_injective outputDimension 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
      rw [map_smul, startupMatrixFirstGraph_base, startupMatrixFirstGraph_base, map_smul, map_smul]
      rfl
  }
  exact mapping.mkContinuous (startupMatrixFirstBudget family) (startupMatrixFirstGraph_bound admissible family coherent)

theorem startupMatrixFirstGraphCLM_norm (admissible : Admissible L sigma gamma ell)
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) :
    ‖startupMatrixFirstGraphCLM admissible family coherent‖ ≤ startupMatrixFirstBudget family := by
  apply ContinuousLinearMap.opNorm_le_bound _ (startupMatrixFirstBudget_nonnegative admissible family)
  exact startupMatrixFirstGraph_bound admissible family coherent

end Grad.CartesianStartup
