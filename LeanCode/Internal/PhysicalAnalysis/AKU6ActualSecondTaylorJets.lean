import AKU4FixedJetLocalization
import AKN16OriginalFlatSourcePrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision Grad.NonlinearRange Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear partialJetLinear_apply partialJet_coordinate_value)

theorem doublePartial_eq_closedDerivative {dimension : ℕ} (field : ClosedJet dimension)
    (first second : Fin 2) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet first
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet second field)).value point =
        closedDerivative field 2 ![first,second] point := by
  change closedDerivative (Grad.NonlinearQuotientBounds.partialJet second field) 1 (fun _ => first) point = _
  rw [partialJet_closedDerivative]
  have wordEq : Fin.append (fun _ : Fin 1 => first) (fun _ : Fin 1 => second) = (![first,second] : CartesianWord 2) := by
    funext index
    fin_cases index <;> rfl
  rw [wordEq]

def scalarSecondTaylorCoefficients (field : ClosedJet 1) : QuadraticScalarCoefficients :=
  ![(Grad.GaugeCoefficients.Physical.Compensated.partialJet 0
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet 0 field)).value closedOrigin 0 / 2,
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet 0
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet 1 field)).value closedOrigin 0,
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet 1
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet 1 field)).value closedOrigin 0 / 2]

/-- The actual second Taylor coefficients of an angular mean-free source
are trace-free. This uses rotation invariance of the genuine axis Laplacian. -/
theorem scalarSecondTaylor_meanFree (field : ClosedJet 1)
    (meanFree : angularClosedJet 0 field = 0) :
    scalarSecondTaylorCoefficients field 0 + scalarSecondTaylorCoefficients field 2 = 0 := by
  have laplace := angularClosedJet_laplacian_origin field
  rw [meanFree] at laplace
  have zero : closedLaplacianValue field closedOrigin = 0 := by
    apply laplace.symm.trans
    change (closedDerivativeLinear 2 (fun _ => 0) (0 : ClosedJet 1)) _ +
      (closedDerivativeLinear 2 (fun _ => 1) (0 : ClosedJet 1)) _ = 0
    rw [map_zero,map_zero]
    simp only [ContinuousMap.zero_apply,add_zero]
  have scalarZero := congrArg (fun value : ComplexEuclidean 1 => value 0) zero
  change closedDerivative field 2 (fun _ => 0) closedOrigin 0 +
    closedDerivative field 2 (fun _ => 1) closedOrigin 0 = 0 at scalarZero
  change (Grad.GaugeCoefficients.Physical.Compensated.partialJet 0
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet 0 field)).value closedOrigin 0 / 2 +
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet 1
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet 1 field)).value closedOrigin 0 / 2 = 0
  rw [doublePartial_eq_closedDerivative,doublePartial_eq_closedDerivative]
  have word0 : (![0,0] : CartesianWord 2) = fun _ => 0 := by ext index; fin_cases index <;> rfl
  have word1 : (![1,1] : CartesianWord 2) = fun _ => 1 := by ext index; fin_cases index <;> rfl
  rw [word0,word1]
  linear_combination (1/2 : ℂ) * scalarZero

theorem quadraticScalarJet_partial_jet (coefficients : QuadraticScalarCoefficients) (direction : Fin 2) :
    Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (quadraticScalarJet coefficients) =
      coordinateJet 0 (scalarCoefficientJet (if direction = 0 then 2 * coefficients 0 else coefficients 1)) +
      coordinateJet 1 (scalarCoefficientJet (if direction = 0 then coefficients 1 else 2 * coefficients 2)) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  have componentZero : component = 0 := Subsingleton.elim _ _
  subst component
  rw [quadraticScalarJet_partial_value]
  fin_cases direction <;>
    simp [closedJet_value_add,coordinateJet_value,scalarCoefficientJet,constantValueJet_value,Complex.real_smul] <;> ring

theorem quadraticScalarJet_doublePartial (coefficients : QuadraticScalarCoefficients)
    (first second : Fin 2) (point : ClosedDisk) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet first
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet second (quadraticScalarJet coefficients))).value point 0 =
      if first = 0 then (if second = 0 then 2 * coefficients 0 else coefficients 1)
      else (if second = 0 then coefficients 1 else 2 * coefficients 2) := by
  rw [quadraticScalarJet_partial_jet]
  change (partialJetLinear 1 first (_ + _)).value point 0 = _
  rw [map_add,partialJetLinear_apply,partialJetLinear_apply]
  simp only [closedJet_value_add,ContinuousMap.add_apply,partialJet_coordinate_value,
    scalarCoefficientJet,constantValueJet_value,partial_constantValueJet_value,smul_zero,add_zero]
  fin_cases first <;> fin_cases second <;> simp [spatialBasis]

/-- The finite scalar polynomial has exactly the actual second derivatives
of the original full source coefficient, with both mixed derivative orders. -/
theorem scalarSecondTaylor_same_second (field : ClosedJet 1) (first second : Fin 2) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet first
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet second
        (quadraticScalarJet (scalarSecondTaylorCoefficients field)))).value closedOrigin =
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet first
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet second field)).value closedOrigin := by
  apply PiLp.ext
  intro component
  have componentZero : component = 0 := Subsingleton.elim _ _
  subst component
  rw [quadraticScalarJet_doublePartial]
  fin_cases first <;> fin_cases second <;> simp [scalarSecondTaylorCoefficients]
  all_goals first
    | ring
    | exact congrArg (fun jet : ClosedJet 1 => jet.value closedOrigin 0)
        (Grad.ActualMeanInverse.partialJets_commute 0 1 field)

end Grad.FinitePhysicalJetLift
