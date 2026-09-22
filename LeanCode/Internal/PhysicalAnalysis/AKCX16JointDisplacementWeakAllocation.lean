import AKCX15JointSpatialDisplacementRemainder

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct
open Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

theorem startupReservedDerivative_same {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension firstOrder secondOrder firstWeight secondWeight firstReserve secondReserve : ℕ}
    (firstBound : firstReserve ≤ firstWeight) (secondBound : secondReserve ≤ secondWeight)
    (firstIndex : JetIndex firstOrder) (secondIndex : JetIndex secondOrder)
    (first : GraphGrade dimension firstOrder firstWeight openUnitDisk)
    (second : GraphGrade dimension secondOrder secondWeight openUnitDisk)
    (reserveSame : firstReserve = secondReserve)
    (same : Realization.recoveredDerivative dimension firstOrder openUnitDisk (fun _ => firstWeight) firstIndex first =
      Realization.recoveredDerivative dimension secondOrder openUnitDisk (fun _ => secondWeight) secondIndex second) :
    startupReservedDerivative admissible firstBound firstIndex first =
      startupReservedDerivative admissible secondBound secondIndex second := by
  apply startupField_ae_ext
  filter_upwards [startupReservedDerivative_ae admissible firstBound firstIndex first,
    startupReservedDerivative_ae admissible secondBound secondIndex second] with point left right
  intro cell
  rw [left cell,right cell,reserveSame,same]

/-- Joint weak spatial allocation for the literal positive or zero axial
displacement kernel; every coefficient derivative remains in the sum. -/
theorem startupDisplacement_orderedWeak {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order rank weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (word : Word rank) (bound : rank ≤ order) (reserve : rank-1 ≤ weight)
    (field : GraphGrade input order weight openUnitDisk) :
    HasWeakOrderedDerivative output openUnitDisk rank word
      (startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
        (base input order openUnitDisk (fun _ => weight) field))
      (∑ selected : Finset (Fin rank),
        startupDisplacementKernel admissible family coherent (startupSelectedCoefficientIndex word selected) power
          (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
            (startupComplementIndex word bound selected) field)) := by
  have paid : cartesianOrder (0,0)+rank-1 ≤ weight := by simpa only [cartesianOrder,zero_add] using reserve
  have weak := startupDisplacementMatrix_baselineWeak admissible family coherent (0,0) power word bound paid field
  have initial : startupDisplacementKernel admissible family coherent (startupShiftedIndex (0,0) (0,0)) power
      (startupReservedDerivative admissible (startupShiftedZero_reserve (0,0) paid) (zeroIndex order) field) =
      startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
        (base input order openUnitDisk (fun _ => weight) field) := by
    change startupDisplacementKernel admissible family coherent zeroDerivativeIndex power
      (startupReservedDerivative admissible (Nat.zero_le weight) (zeroIndex order) field) = _
    rw [startupReservedDerivative_zero,Realization.recoveredDerivative_zero]
  have terms : (∑ selected : Finset (Fin rank),
      startupDisplacementKernel admissible family coherent (startupShiftedIndex (0,0) (selectedIndex word selected)) power
        (startupReservedDerivative admissible (startupShiftedSelected_reserve (0,0) word selected paid)
          (startupComplementIndex word bound selected) field)) =
      ∑ selected : Finset (Fin rank),
        startupDisplacementKernel admissible family coherent (startupSelectedCoefficientIndex word selected) power
          (startupReservedDerivative admissible (startupSelectedCoefficientIndex_reserve word selected reserve)
            (startupComplementIndex word bound selected) field) := by
    apply Finset.sum_congr rfl
    intro selected _
    have indexSame : derivativeMultiIndex (startupShiftedIndex (0,0) (selectedIndex word selected)) =
        derivativeMultiIndex (startupSelectedCoefficientIndex word selected) := by
      simp only [startupShiftedIndex,derivativeMultiIndex_top,Nat.add_zero,startupSelectedCoefficientIndex_multi]
    have orderSame : derivativeOrder (startupShiftedIndex (0,0) (selectedIndex word selected)) =
        derivativeOrder (startupSelectedCoefficientIndex word selected) :=
      congrArg (fun pair : ℕ × ℕ => pair.1+pair.2) indexSame
    rw [startupDisplacementKernel_multi_congr admissible family coherent _ _ indexSame power]
    congr 1
  rw [initial,terms] at weak
  exact weak

end Grad.CartesianStartup
