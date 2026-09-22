import SeedCoefficientLinear

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open scoped ContDiff BigOperators

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Frame

local instance seedParameterComplexSpace (phase : PhaseParameters) (grade input output : ℕ) :
    NormedSpace ℂ (Coefficient 1 phase.sigma0 phase.gamma 1 grade input output) := inferInstance
local instance seedParameterRealSpace (phase : PhaseParameters) (grade input output : ℕ) :
    NormedSpace ℝ (Coefficient 1 phase.sigma0 phase.gamma 1 grade input output) := inferInstance

@[fun_prop] theorem parameter_complex_contDiff (index : Fin 4) :
    ContDiff ℝ ∞ (fun parameter : Parameters => (parameter index : ℂ)) := by
  have coordinate : ContDiff ℝ ∞ (fun parameter : Parameters => parameter index) := by fun_prop
  exact Complex.ofRealCLM.contDiff.comp coordinate

theorem seedAmplitude_contDiff (sign : ℝ) (mode : Fin 5) :
    ContDiff ℝ ∞ (fun parameter : Parameters => seedLaurentAmplitude sign (parameter 1) (parameter 2) (parameter 3) mode) := by
  fin_cases mode <;> norm_num [seedLaurentAmplitude] <;> fun_prop

theorem seedGenerator_contDiff (phase : PhaseParameters) (grade : ℕ) (sign : ℝ) :
    ContDiff ℝ ∞ (fun parameter : Parameters =>
      seedAngleGenerator 1 phase.sigma0 phase.gamma 1 grade sign (parameter 1) (parameter 2) (parameter 3)) := by
  unfold seedAngleGenerator
  apply ContDiff.sum
  intro mode _
  have smooth := ((constantCellCLM (seedAdmissible phase) grade 1 1 (seedLaurentCell mode)).restrictScalars ℝ).contDiff.comp
    ((seedAmplitude_contDiff sign mode).smul (contDiff_const : ContDiff ℝ ∞
      (fun _ : Parameters => ContinuousLinearMap.id ℂ (ComplexEuclidean 1))))
  exact smooth

theorem seedAngleExp_contDiff (phase : PhaseParameters) (grade : ℕ) (sign : ℝ) :
    ContDiff ℝ ∞ (fun parameter : Parameters =>
      seedAngleExponential (seedAdmissible phase) grade sign (parameter 1) (parameter 2) (parameter 3)) := by
  exact (seedExponential_contDiff (seedAdmissible phase) grade 1).comp (seedGenerator_contDiff phase grade sign)

theorem positiveRoot_contDiffOn :
    ContDiffOn ℝ ∞ (fun parameter : Parameters => Real.sqrt (1 + parameter 0)) parameterDomain := by
  apply (show ContDiff ℝ ∞ (fun parameter : Parameters => 1 + parameter 0) by fun_prop).contDiffOn.sqrt
  intro parameter inside
  have interval := abs_lt.mp (show |parameter 0| < 1 from inside)
  linarith

theorem negativeRoot_contDiffOn :
    ContDiffOn ℝ ∞ (fun parameter : Parameters => Real.sqrt (1 - parameter 0)) parameterDomain := by
  apply (show ContDiff ℝ ∞ (fun parameter : Parameters => 1 - parameter 0) by fun_prop).contDiffOn.sqrt
  intro parameter inside
  have interval := abs_lt.mp (show |parameter 0| < 1 from inside)
  linarith

theorem isotropic_contDiffOn :
    ContDiffOn ℝ ∞ (fun parameter : Parameters => seedIsotropic (parameter 0)) parameterDomain := by
  exact (positiveRoot_contDiffOn.add negativeRoot_contDiffOn).div_const 2

theorem anisotropic_contDiffOn :
    ContDiffOn ℝ ∞ (fun parameter : Parameters => seedAnisotropic (parameter 0)) parameterDomain := by
  exact (positiveRoot_contDiffOn.sub negativeRoot_contDiffOn).div_const 2

theorem seedDeviation_contDiffOn (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (fun parameter : Parameters => seedMatrixDeviationCoefficient (seedAdmissible phase) grade
      (parameter 0) (parameter 1) (parameter 2) (parameter 3)) parameterDomain := by
  have scalarConstant : ContDiffOn ℝ ∞
      (fun parameter : Parameters => (((seedIsotropic (parameter 0) - 1 : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ (ComplexEuclidean 2))) parameterDomain := by
    have scalarSmooth : ContDiffOn ℝ ∞ (fun parameter : Parameters => ((seedIsotropic (parameter 0) - 1 : ℝ) : ℂ)) parameterDomain :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (isotropic_contDiffOn.sub contDiffOn_const)
    exact scalarSmooth.smul (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Parameters => ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) parameterDomain)
  have constantSmooth := ((constantCellCLM (seedAdmissible phase) grade 2 2 0).restrictScalars ℝ).contDiff.comp_contDiffOn scalarConstant
  have plusSmooth := ((scalarLiftCLM (seedAdmissible phase) grade seedPlusMatrix).restrictScalars ℝ).contDiff.comp
    (seedAngleExp_contDiff phase grade 1)
  have minusSmooth := ((scalarLiftCLM (seedAdmissible phase) grade seedMinusMatrix).restrictScalars ℝ).contDiff.comp
    (seedAngleExp_contDiff phase grade (-1))
  have anisotropicSmooth := Complex.ofRealCLM.contDiff.comp_contDiffOn anisotropic_contDiffOn
  exact constantSmooth.add (anisotropicSmooth.smul (plusSmooth.add minusSmooth).contDiffOn)

theorem inverseDeterminant_contDiffOn :
    ContDiffOn ℝ ∞ (fun parameter : Parameters => inverseDeterminant (parameter 0)) parameterDomain := by
  have squareSmooth : ContDiff ℝ ∞ (fun parameter : Parameters => 1 - parameter 0 ^ 2) := by fun_prop
  have positive (parameter : Parameters) (inside : parameter ∈ parameterDomain) : 0 < 1 - parameter 0 ^ 2 := by
    have interval := abs_lt.mp (show |parameter 0| < 1 from inside)
    nlinarith
  have root := squareSmooth.contDiffOn.sqrt (fun parameter inside => (positive parameter inside).ne')
  exact root.inv (fun parameter inside => (Real.sqrt_pos.mpr (positive parameter inside)).ne')

def reflectedParameters (parameter : Parameters) : Parameters :=
  ![-parameter 0, parameter 1, parameter 2, parameter 3]

theorem reflectedParameters_contDiff : ContDiff ℝ ∞ reflectedParameters := by
  rw [contDiff_pi]
  intro coordinate
  fin_cases coordinate <;> norm_num [reflectedParameters] <;> fun_prop

theorem reflectedParameters_mapsTo : Set.MapsTo reflectedParameters parameterDomain parameterDomain := by
  intro parameter inside
  change |-(parameter 0)| < 1
  rw [abs_neg]
  exact inside

theorem inverseDeviation_contDiffOn (phase : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (inverseDeviationCoefficient phase grade) parameterDomain := by
  have inverseSmooth := Complex.ofRealCLM.contDiff.comp_contDiffOn inverseDeterminant_contDiffOn
  have reflectedSmooth := (seedDeviation_contDiffOn phase grade).comp
    reflectedParameters_contDiff.contDiffOn reflectedParameters_mapsTo
  have constantInput : ContDiffOn ℝ ∞ (fun parameter : Parameters =>
      (((inverseDeterminant (parameter 0) - 1 : ℝ) : ℂ) • ContinuousLinearMap.id ℂ (ComplexEuclidean 2))) parameterDomain :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (inverseDeterminant_contDiffOn.sub contDiffOn_const)).smul contDiffOn_const
  have constantSmooth := ((constantCellCLM (seedAdmissible phase) grade 2 2 0).restrictScalars ℝ).contDiff.comp_contDiffOn constantInput
  exact (inverseSmooth.smul reflectedSmooth).add constantSmooth

end Grad.Constraints.Seed
