import AKU6ActualSecondTaylorJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear partialJetLinear_apply partialJet_coordinate_value)

theorem partial_coordinateJet {dimension : ℕ} (direction coordinate : Fin 2) (field : ClosedJet dimension) :
    Grad.GaugeCoefficients.Physical.Compensated.partialJet direction (coordinateJet coordinate field) =
      (spatialBasis direction coordinate : ℂ) • field +
        coordinateJet coordinate (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [partialJet_coordinate_value]
  rw [closedJet_value_add,ContinuousMap.add_apply,closedJet_value_smul,
    ContinuousMap.smul_apply,coordinateJet_value,Complex.coe_smul]

theorem doublePartial_coordinate_axis {dimension : ℕ} (first second coordinate : Fin 2)
    (field : ClosedJet dimension) :
    (Grad.GaugeCoefficients.Physical.Compensated.partialJet first
      (Grad.GaugeCoefficients.Physical.Compensated.partialJet second (coordinateJet coordinate field))).value closedOrigin =
      (spatialBasis second coordinate : ℂ) •
        (Grad.GaugeCoefficients.Physical.Compensated.partialJet first field).value closedOrigin +
      (spatialBasis first coordinate : ℂ) •
        (Grad.GaugeCoefficients.Physical.Compensated.partialJet second field).value closedOrigin := by
  rw [partial_coordinateJet]
  change (partialJetLinear dimension first (_ + _)).value closedOrigin = _
  rw [map_add,map_smul,partialJetLinear_apply,partialJetLinear_apply,partial_coordinateJet]
  simp only [closedJet_value_add,closedJet_value_smul,ContinuousMap.add_apply,
    ContinuousMap.smul_apply,coordinateJet_value,closedOrigin,PiLp.zero_apply,zero_smul,add_zero]

theorem laplacian_coordinate_axis {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    closedLaplacianValue (coordinateJet coordinate field) closedOrigin =
      (2 : ℂ) • (Grad.GaugeCoefficients.Physical.Compensated.partialJet coordinate field).value closedOrigin := by
  have word0 : (![0,0] : CartesianWord 2) = fun _ => 0 := by ext index; fin_cases index <;> rfl
  have word1 : (![1,1] : CartesianWord 2) = fun _ => 1 := by ext index; fin_cases index <;> rfl
  rw [closedLaplacianValue,← word0,← word1,← doublePartial_eq_closedDerivative,
    ← doublePartial_eq_closedDerivative,doublePartial_coordinate_axis,doublePartial_coordinate_axis]
  fin_cases coordinate <;> simp [spatialBasis] <;> module

def axisFirstMatrix (field : ClosedJet 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun component direction => (Grad.GaugeCoefficients.Physical.Compensated.partialJet direction field).value closedOrigin component

def planarRadialContractionJet (field : ClosedJet 2) : ClosedJet 1 :=
  coordinateJet 0 (valueMapJet (Grad.FlatSourceProjection.componentValue 2 0) field) +
    coordinateJet 1 (valueMapJet (Grad.FlatSourceProjection.componentValue 2 1) field)

theorem planarRadialContractionJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (planarRadialContractionJet field).value point 0 =
      (point.val 0 : ℂ) * field.value point 0 + (point.val 1 : ℂ) * field.value point 1 := by
  simp [planarRadialContractionJet,closedJet_value_add,coordinateJet_value,valueMapJet_value,Complex.real_smul]

/-- A zero radial mean forces the actual trace-free first Cartesian jet. -/
theorem axisFirstMatrix_traceFree (field : ClosedJet 2)
    (radialMean : angularClosedJet 0 (planarRadialContractionJet field) = 0) :
    axisFirstMatrix field 0 0 + axisFirstMatrix field 1 1 = 0 := by
  have laplace := angularClosedJet_laplacian_origin (planarRadialContractionJet field)
  rw [radialMean] at laplace
  have zero : closedLaplacianValue (planarRadialContractionJet field) closedOrigin = 0 := by
    apply laplace.symm.trans
    change (closedDerivativeLinear 2 (fun _ => 0) (0 : ClosedJet 1)) _ +
      (closedDerivativeLinear 2 (fun _ => 1) (0 : ClosedJet 1)) _ = 0
    rw [map_zero,map_zero]
    simp only [ContinuousMap.zero_apply,add_zero]
  have addLaplace {dimension : ℕ} (first second : ClosedJet dimension) :
      closedLaplacianValue (first + second) closedOrigin =
        closedLaplacianValue first closedOrigin + closedLaplacianValue second closedOrigin := by
    change (closedDerivativeLinear 2 (fun _ => 0) (first + second)) _ +
      (closedDerivativeLinear 2 (fun _ => 1) (first + second)) _ = _
    rw [map_add,map_add]
    simp only [ContinuousMap.add_apply]
    simp only [closedDerivativeLinear,LinearMap.coe_mk,AddHom.coe_mk]
    unfold closedLaplacianValue
    abel
  rw [planarRadialContractionJet,addLaplace,laplacian_coordinate_axis,laplacian_coordinate_axis,
    Grad.GaugeCoefficients.Physical.Compensated.partialJet_valueMap,
    Grad.GaugeCoefficients.Physical.Compensated.partialJet_valueMap,valueMapJet_value,valueMapJet_value] at zero
  have scalarZero := congrArg (fun value : ComplexEuclidean 1 => value 0) zero
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,Grad.FlatSourceProjection.componentValue_apply,PiLp.zero_apply] at scalarZero
  change 2 * axisFirstMatrix field 0 0 + 2 * axisFirstMatrix field 1 1 = 0 at scalarZero
  linear_combination (1/2 : ℂ) * scalarZero

end Grad.FinitePhysicalJetLift
