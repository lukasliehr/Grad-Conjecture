import AKCB4ActualFullOrderedMatrixWeak
import AKCC23FixedTensorExactDerivativeSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

theorem startupDerivativeKernel_multi_congr {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {firstGrade secondGrade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (first : Grad.GaugeCoefficients.Algebra.DerivativeIndex firstGrade)
    (second : Grad.GaugeCoefficients.Algebra.DerivativeIndex secondGrade)
    (same : derivativeMultiIndex first = derivativeMultiIndex second) :
    startupDerivativeKernel admissible family coherent first = startupDerivativeKernel admissible family coherent second := by
  have orderSame : derivativeOrder first = derivativeOrder second := congrArg (fun pair : ℕ × ℕ => pair.1 + pair.2) same
  unfold startupDerivativeKernel
  refine startupKernel_congr _ _ ?_ ?_
  · rfl
  · intro outer inner
    filter_upwards [] with pair
    change closedDiskLift (startupDerivativeCoefficient admissible family coherent first inner (outer-inner)) pair.2 = _
    simp only [startupDerivativeKernelData, startupDerivativeCoefficient, same, orderSame]

theorem startupReservedDerivative_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension order weight : ℕ}
    (bound : 0 ≤ weight) (index : JetIndex order) (field : GraphGrade dimension order weight openUnitDisk) :
    startupReservedDerivative admissible bound index field =
      Realization.recoveredDerivative dimension order openUnitDisk (fun _ => weight) index field := by
  apply startupField_ae_ext
  filter_upwards [startupReservedDerivative_ae admissible bound index field] with point represented
  intro cell
  simpa only [pow_zero, Complex.ofReal_one, one_smul] using represented cell

theorem startupActualMatrix_emptyAllocation {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (word : Word rank) (bound : rank ≤ order) (reserve : rank - 1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    startupDerivativeKernel admissible family coherent (startupSelectedCoefficientIndex word ∅)
      (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word ∅ reserve)
        (startupComplementIndex word bound ∅) field) =
      originalMatrixKernel admissible family coherent
        (orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word) := by
  have indexSame : derivativeMultiIndex (startupSelectedCoefficientIndex word ∅) = derivativeMultiIndex zeroDerivativeIndex := by
    rw [startupSelectedCoefficientIndex_multi, startupEmpty_selectedIndex]
    rfl
  have inputSame : startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word ∅ reserve)
      (startupComplementIndex word bound ∅) field =
      orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word := by
    have noReserve : derivativeOrder (startupSelectedCoefficientIndex word ∅) - 1 = 0 := by
      rw [startupSelectedCoefficientIndex_order]
      rfl
    have realized := startupReservedDerivative_ae admissible
      (startupSelectedCoefficientIndex_reserve word ∅ reserve) (startupComplementIndex word bound ∅) field
    have recovered : Realization.recoveredDerivative input order openUnitDisk (fun _ => weight)
      (startupComplementIndex word bound ∅) field =
      orderedDerivative input order rank openUnitDisk (fun _ => weight) bound field word := by
      rw [← startupInputDerivative_recovered]
      rw [startupFull_subword]
      exact startupEmpty_inputDerivative bound field word
    apply startupField_ae_ext
    filter_upwards [realized] with point same
    intro cell
    rw [same cell, noReserve, pow_zero, Complex.ofReal_one, one_smul, recovered]
  rw [startupDerivativeKernel_multi_congr admissible family coherent _ _ indexSame, inputSame]
  rfl

end Grad.CartesianStartup
