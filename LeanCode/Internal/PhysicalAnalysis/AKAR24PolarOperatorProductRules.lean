import AKAR22LiteralAngularCommutators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryLift Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Ledger

variable {input middle output : ℕ}

def OriginalCircleOperatorDerivative (operator derivative : CellL2 input →L[ℂ] CellL2 output) : Prop :=
  ∀ field rotated, OriginalCircleRotation field rotated →
    OriginalCircleRotation (operator field) (derivative field+operator rotated)

theorem OriginalCircleOperatorDerivative.comp
    {outer outerR : CellL2 middle →L[ℂ] CellL2 output} {inner innerR : CellL2 input →L[ℂ] CellL2 middle}
    (one : OriginalCircleOperatorDerivative outer outerR) (two : OriginalCircleOperatorDerivative inner innerR) :
    OriginalCircleOperatorDerivative (outer.comp inner) (outerR.comp inner+outer.comp innerR) := by
  intro field rotated rotation
  have result := one (inner field) (innerR field+inner rotated) (two field rotated rotation)
  simpa only [ContinuousLinearMap.comp_apply,add_apply,map_add,add_assoc] using result

theorem OriginalCircleOperatorDerivative.add
    {first firstR second secondR : CellL2 input →L[ℂ] CellL2 output}
    (one : OriginalCircleOperatorDerivative first firstR) (two : OriginalCircleOperatorDerivative second secondR) :
    OriginalCircleOperatorDerivative (first+second) (firstR+secondR) := by
  intro field rotated rotation
  have result := (one field rotated rotation).add (two field rotated rotation)
  convert result using 1 <;> simp only [add_apply]; abel

theorem OriginalCircleOperatorDerivative.neg
    {operator derivative : CellL2 input →L[ℂ] CellL2 output}
    (original : OriginalCircleOperatorDerivative operator derivative) :
    OriginalCircleOperatorDerivative (-operator) (-derivative) := by
  intro field rotated rotation
  have result := (original field rotated rotation).smul (-1)
  simpa only [neg_apply,neg_one_smul,neg_add_rev,add_comm] using result

theorem originalCircleMatrix_derivative (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    OriginalCircleOperatorDerivative (originalCircleMatrix parameters mapping) 0 := by
  intro field rotated rotation
  simpa only [zero_apply,zero_add] using rotation.valueMap parameters mapping

theorem originalCircleCosine_derivative (parameters : PhaseParameters) (dimension : ℕ) :
    OriginalCircleOperatorDerivative (weightedHilbertCosine parameters dimension 0) (-weightedHilbertSine parameters dimension 0) := by
  intro field rotated rotation
  simpa only [neg_apply,sub_eq_add_neg,add_comm] using rotation.cosine parameters

theorem originalCircleSine_derivative (parameters : PhaseParameters) (dimension : ℕ) :
    OriginalCircleOperatorDerivative (weightedHilbertSine parameters dimension 0) (weightedHilbertCosine parameters dimension 0) := by
  intro field rotated rotation
  simpa only [add_comm] using rotation.sine parameters

theorem originalCircleRadialRow_derivative (parameters : PhaseParameters) :
    OriginalCircleOperatorDerivative (originalCircleRadialRow parameters) (originalCircleTangentialRow parameters) := by
  have one := (originalCircleMatrix_derivative parameters (matrixUnit (input := 3) (output := 1) 0 0)).comp
    (originalCircleCosine_derivative parameters 3)
  have two := (originalCircleMatrix_derivative parameters (matrixUnit (input := 3) (output := 1) 0 1)).comp
    (originalCircleSine_derivative parameters 3)
  convert one.add two using 1
  · rfl
  · ext field
    simp only [originalCircleTangentialRow,ContinuousLinearMap.comp_apply,add_apply,sub_apply,zero_apply,zero_add,neg_apply,map_neg]
    abel

theorem originalCircleTangentialRow_derivative (parameters : PhaseParameters) :
    OriginalCircleOperatorDerivative (originalCircleTangentialRow parameters) (-originalCircleRadialRow parameters) := by
  have one := (originalCircleMatrix_derivative parameters (matrixUnit (input := 3) (output := 1) 0 1)).comp
    (originalCircleCosine_derivative parameters 3)
  have two := ((originalCircleMatrix_derivative parameters (matrixUnit (input := 3) (output := 1) 0 0)).comp
    (originalCircleSine_derivative parameters 3)).neg
  convert one.add two using 1
  · ext field
    simp only [originalCircleTangentialRow,sub_eq_add_neg,add_apply,neg_apply]
  · ext field
    simp only [originalCircleRadialRow,ContinuousLinearMap.comp_apply,add_apply,zero_apply,zero_add,neg_apply,map_neg]
    abel

theorem originalCircleRadialColumn_derivative (parameters : PhaseParameters) :
    OriginalCircleOperatorDerivative (originalCircleRadialColumn parameters) (originalCircleTangentialColumn parameters) := by
  have one := (originalCircleMatrix_derivative parameters (matrixUnit (input := 1) (output := 3) 0 0)).comp
    (originalCircleCosine_derivative parameters 1)
  have two := (originalCircleMatrix_derivative parameters (matrixUnit (input := 1) (output := 3) 1 0)).comp
    (originalCircleSine_derivative parameters 1)
  convert one.add two using 1
  · rfl
  · ext field
    simp only [originalCircleTangentialColumn,ContinuousLinearMap.comp_apply,add_apply,sub_apply,zero_apply,zero_add,neg_apply,map_neg]
    abel

theorem originalCircleFamilyAction_derivative (parameters : PhaseParameters)
    (family : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : Grad.GaugeCoefficients.Physical.Allocation.FamilyCoherent family) (radius : RadialPoint) :
    OriginalCircleOperatorDerivative (originalCircleFamilyAction parameters family coherent radius)
      (originalCircleFamilyAngularAction parameters family coherent radius) := by
  intro field rotated rotation
  exact rotation.kernel parameters radius _

end Grad.OriginalKernelRetainedDecay
