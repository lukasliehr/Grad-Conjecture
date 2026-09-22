import AKAR18ActualSmoothCircleConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.BoundaryLift Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarAngular
open Grad.ActualSmoothPhysicalField Grad.AnnularGeneralSourceRegularity Grad.GaugeCoefficients.Physical.Ledger

variable {dimension : ℕ} {parameters : PhaseParameters} {radius : RadialPoint}

theorem OriginalCircleRepresents.add {first second : CellL2 dimension}
    {source target : ℝ × ℝ → ComplexEuclidean dimension}
    (one : OriginalCircleRepresents parameters radius first source) (two : OriginalCircleRepresents parameters radius second target)
    (sourceContinuous : Continuous source) (targetContinuous : Continuous target) :
    OriginalCircleRepresents parameters radius (first+second) (fun angles => source angles+target angles) := by
  intro mode
  rw [doubleCoefficient_add _ _ sourceContinuous targetContinuous]
  change (_ : ℂ) • (first mode+second mode) = _
  rw [smul_add]
  exact congrArg₂ (·+·) (one mode) (two mode)

theorem OriginalCircleRepresents.sub {first second : CellL2 dimension}
    {source target : ℝ × ℝ → ComplexEuclidean dimension}
    (one : OriginalCircleRepresents parameters radius first source) (two : OriginalCircleRepresents parameters radius second target)
    (sourceContinuous : Continuous source) (targetContinuous : Continuous target) :
    OriginalCircleRepresents parameters radius (first-second) (fun angles => source angles-target angles) := by
  intro mode
  rw [doubleCoefficient_sub _ _ sourceContinuous targetContinuous]
  change (_ : ℂ) • (first mode-second mode) = _
  rw [smul_sub]
  exact congrArg₂ (·-·) (one mode) (two mode)

theorem OriginalCircleRepresents.smul {field : CellL2 dimension} {source : ℝ × ℝ → ComplexEuclidean dimension}
    (represented : OriginalCircleRepresents parameters radius field source) (scalar : ℂ) :
    OriginalCircleRepresents parameters radius (scalar • field) (fun angles => scalar • source angles) := by
  intro mode
  have double : doubleCoefficient (fun angles => scalar • source angles) mode = scalar • doubleCoefficient source mode := by
    unfold doubleCoefficient
    have inner (polar : ℝ) : angularCoefficient (fun axial => scalar • source (polar,axial)) mode.2 =
        scalar • angularCoefficient (fun axial => source (polar,axial)) mode.2 := angularCoefficient_smul_continuous scalar _ _
    simp_rw [inner]
    exact angularCoefficient_smul_continuous scalar _ _
  rw [double]
  change (_ : ℂ) • (scalar • field mode) = _
  rw [smul_comm]
  exact congrArg (scalar • ·) (represented mode)

theorem OriginalCircleRepresents.valueMap {output : ℕ} {field : CellL2 dimension}
    {source : ℝ × ℝ → ComplexEuclidean dimension}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source)
    (mapping : ComplexEuclidean dimension →L[ℂ] ComplexEuclidean output) :
    OriginalCircleRepresents parameters radius (originalCircleMatrix parameters mapping field) (fun angles => mapping (source angles)) := by
  intro mode
  rw [doubleCoefficient_valueMap mapping source continuousSource]
  change (_ : ℂ) • mapping (field mode) = _
  rw [← map_smul]
  exact congrArg mapping (represented mode)

theorem OriginalCircleRepresents.cosine {field : CellL2 dimension} {source : ℝ × ℝ → ComplexEuclidean dimension}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source) :
    OriginalCircleRepresents parameters radius (weightedHilbertCosine parameters dimension 0 field)
      (fun angles => (Real.cos angles.1 : ℂ) • source angles) := by
  intro mode
  rw [doubleCoefficient_cosine source continuousSource]
  change (_ : ℂ) • ((2 : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • field (mode.1-1,mode.2)+annularShiftScalar 0 (-1) mode • field (mode.1-(-1),mode.2))) = _
  simp only [annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul]
  rw [smul_comm,smul_add]
  change (2 : ℂ)⁻¹ • (lambdaCircleCoefficient parameters radius.val field (mode.1-1,mode.2)+
    lambdaCircleCoefficient parameters radius.val field (mode.1-(-1),mode.2)) = _
  rw [represented,represented]
  simp only [sub_neg_eq_add]

theorem OriginalCircleRepresents.sine {field : CellL2 dimension} {source : ℝ × ℝ → ComplexEuclidean dimension}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source) :
    OriginalCircleRepresents parameters radius (weightedHilbertSine parameters dimension 0 field)
      (fun angles => (Real.sin angles.1 : ℂ) • source angles) := by
  intro mode
  rw [doubleCoefficient_sine source continuousSource]
  change (_ : ℂ) • ((2*Complex.I : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • field (mode.1-1,mode.2)-annularShiftScalar 0 (-1) mode • field (mode.1-(-1),mode.2))) = _
  simp only [annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul]
  rw [smul_comm,smul_sub]
  change (2*Complex.I : ℂ)⁻¹ • (lambdaCircleCoefficient parameters radius.val field (mode.1-1,mode.2)-
    lambdaCircleCoefficient parameters radius.val field (mode.1-(-1),mode.2)) = _
  rw [represented,represented]
  simp only [sub_neg_eq_add]

def originalPolarRadialValue (value : ComplexEuclidean 3) (angle : ℝ) : ComplexEuclidean 1 :=
  matrixUnit 0 0 ((Real.cos angle : ℂ) • value)+matrixUnit 0 1 ((Real.sin angle : ℂ) • value)
def originalPolarTangentialValue (value : ComplexEuclidean 3) (angle : ℝ) : ComplexEuclidean 1 :=
  matrixUnit 0 1 ((Real.cos angle : ℂ) • value)-matrixUnit 0 0 ((Real.sin angle : ℂ) • value)

theorem OriginalCircleRepresents.radial {field : CellL2 3} {source : ℝ × ℝ → ComplexEuclidean 3}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source) :
    OriginalCircleRepresents parameters radius (originalCircleRadialRow parameters field)
      (fun angles => originalPolarRadialValue (source angles) angles.1) := by
  exact ((represented.cosine continuousSource).valueMap (by fun_prop) (matrixUnit 0 0)).add
    ((represented.sine continuousSource).valueMap (by fun_prop) (matrixUnit 0 1)) (by fun_prop) (by fun_prop)

theorem OriginalCircleRepresents.tangential {field : CellL2 3} {source : ℝ × ℝ → ComplexEuclidean 3}
    (represented : OriginalCircleRepresents parameters radius field source) (continuousSource : Continuous source) :
    OriginalCircleRepresents parameters radius (originalCircleTangentialRow parameters field)
      (fun angles => originalPolarTangentialValue (source angles) angles.1) := by
  exact ((represented.cosine continuousSource).valueMap (by fun_prop) (matrixUnit 0 1)).sub
    ((represented.sine continuousSource).valueMap (by fun_prop) (matrixUnit 0 0)) (by fun_prop) (by fun_prop)

end Grad.OriginalKernelRetainedDecay
