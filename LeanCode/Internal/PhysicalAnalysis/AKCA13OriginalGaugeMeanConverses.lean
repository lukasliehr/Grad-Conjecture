import AKCA12PuncturedOriginalCoreFaithfulness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped BigOperators
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.SourceCollar Grad.SourceCollarFullSource Grad.BoundaryTrace
open Grad.OriginalKernelCovariantRecovery Grad.ChartAxisLift Grad.PhysicalCoordinates
open Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualGaugeSigmaPrimitives

 theorem tangentialCore_zero_of_physicalMeans (parameters : PhaseParameters) (field : ACore parameters 2)
    (means : ∀ (radius : ℝ),0 < radius → ∀ bounded : |radius|≤1,∀ axial,
      sourceAngularAverage (fun polar => polarTangentialComponent polar
        (coreValue field (polarClosedPoint radius bounded polar) axial))=0) :
    tangentialCore parameters field=0 := by
  apply Subtype.ext
  funext cell
  change tangentialJet (field.val cell)=0
  apply closedJet_zero_of_punctured
  intro point nonzero
  let radius := ‖point.val‖
  have bounded : |radius|≤1 := by dsimp only [radius]; rw [abs_norm]; exact point.property
  have axisZero : ((tangentialCore parameters field).val cell).value (axisClosedPoint radius bounded) 1=0 :=
    coreValue_coordinate_zero parameters (tangentialCore parameters field) (axisClosedPoint radius bounded) 1
      (fun axial => (sourceAngularAverage_polarTangential field radius bounded axial).symm.trans
        (means radius nonzero bounded axial)) cell
  rw [originalTangentialCore_axis_value] at axisZero
  obtain ⟨angle,same⟩ := closedPoint_has_polar_angle point
  rw [← same,tangentialJet_polar_formula,polarTangentialMean_independent,axisZero,zero_smul]

 theorem angularCore_zero_of_physicalMeans (parameters : PhaseParameters) (field : ACore parameters 1)
    (means : ∀ (radius : ℝ),0 < radius → ∀ bounded : |radius|≤1,∀ axial,
      sourceAngularAverage (fun polar => coreValue field (polarClosedPoint radius bounded polar) axial 0)=0) :
    angularCore parameters 0 field=0 := by
  apply Subtype.ext
  funext cell
  change angularClosedJet 0 (field.val cell)=0
  apply closedJet_zero_of_punctured
  intro point nonzero
  let radius := ‖point.val‖
  have bounded : |radius|≤1 := by dsimp only [radius]; rw [abs_norm]; exact point.property
  have axisZero : ((angularCore parameters 0 field).val cell).value (axisClosedPoint radius bounded)=0 := by
    apply PiLp.ext
    intro coordinate
    obtain rfl := Fin.eq_zero coordinate
    exact coreValue_coordinate_zero parameters (angularCore parameters 0 field) (axisClosedPoint radius bounded) 0
      (fun axial => (sourceAngularAverage_sourceCoreValue field radius bounded axial).symm.trans
        (means radius nonzero bounded axial)) cell
  obtain ⟨angle,same⟩ := closedPoint_has_polar_angle point
  rw [← same]
  change (angularClosedJet 0 (field.val cell)).value
    (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded))=0
  rw [angularClosedJet_rotation_value,← angularCore_apply,axisZero,smul_zero]

 theorem originalGauges_zero_of_covectorMeans (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed∈Seed.parameterDomain) (vector : ACore parameters 3)
    (means : ∀ radius : ℝ,0 < radius → ∀ bounded : |radius|≤1,∀ axial kind,
      sourceAngularAverage (fun polar => ∑ coordinate : Fin 3,
        physicalGaugeCovector (operatorMatrix (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) axial))
          ((parameters.length : ℂ)⁻¹ • operatorMatrix (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) axial))
          polar (polarClosedPoint radius bounded polar) kind coordinate *
          coreValue vector (polarClosedPoint radius bounded polar) axial coordinate)=0) :
    poloidalCorrection parameters seed inside (toPhysicalCore parameters vector)=0 ∧
    toroidalCorrection parameters seed inside (toPhysicalCore parameters vector)=0 := by
  constructor
  · have projected : tangentialCore parameters (seedTransposeCore parameters seed inside
        (planarPartCore parameters (toPhysicalCore parameters vector)))=0 := by
      apply tangentialCore_zero_of_physicalMeans
      intro radius positive bounded axial
      have mean := means radius positive bounded axial 0
      simp_rw [← operatorMatrix_smul,originalPoloidalCovector_storage] at mean
      simpa only [coreValue_seedTranspose,planarPartCore,coreValue_gaugeValueMap,
        toPhysicalCore,coreValue_valueMap] using mean
    rw [poloidalCorrection_apply,projected,map_zero,map_zero]
  · have projected : angularCore parameters 0 (toroidalPartCore parameters (toPhysicalCore parameters vector)+
        (parameters.length⁻¹ : ℂ) • derivativeDotCore parameters seed inside
          (planarPartCore parameters (toPhysicalCore parameters vector)))=0 := by
      apply angularCore_zero_of_physicalMeans
      intro radius positive bounded axial
      have mean := means radius positive bounded axial 1
      simp_rw [originalToroidalCovector_storage] at mean
      simpa only [coreValue_add,coreValue_smul,coreValue_derivativeDot,
        planarPartCore,toroidalPartCore,coreValue_gaugeValueMap,toPhysicalCore,coreValue_valueMap] using mean
    rw [toroidalCorrection_apply,projected,map_zero]

end Grad.OriginalCoreRealization
