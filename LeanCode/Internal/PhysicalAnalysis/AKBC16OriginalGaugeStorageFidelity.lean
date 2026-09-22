import AKBC15LiteralGaugeCovectorPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
open scoped BigOperators
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.SourceCollar Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.FlatSourceProjection
open Grad.Cor18 Grad.ChartAxisLift Grad.PhysicalCoordinates Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualGaugeSigmaPrimitives

 theorem coreValue_gaugeValueMap {parameters : PhaseParameters} {input output : ℕ}
    (mapping : ComplexEuclidean input→L[ℂ]ComplexEuclidean output) (field : ACore parameters input)
    (point : ClosedDisk) (angle : ℝ) :
    coreValue (Grad.Constraints.valueMapCore mapping parameters field) point angle=mapping (coreValue field point angle) := by
  unfold coreValue
  simp_rw [Grad.Constraints.valueMapCore_apply,valueMapJet_value,← map_smul]
  exact (mapping.map_tsum (coreValue_summable field point angle)).symm

theorem originalPlanarBasis (column : Fin 2) :
    (WithLp.toLp 2 (fun index : Fin 2 => if index=column then (1 : ℂ) else 0))=PiLp.single 2 column 1 := by
  apply PiLp.ext
  intro index
  simp [PiLp.single_apply,eq_comm]

theorem originalPoloidalCovector_storage (seed derivative : ComplexEuclidean 2→L[ℂ]ComplexEuclidean 2)
    (angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    (∑ coordinate : Fin 3,physicalGaugeCovector (operatorMatrix seed) (operatorMatrix derivative) angle point 0 coordinate*value coordinate)=
      polarTangentialComponent angle (transposeOperator seed (planarPartMap (toPhysicalValue value))) := by
  simp [physicalGaugeCovector,planarPhysicalInclusion,Matrix.mulVec,dotProduct,Fin.sum_univ_three,Fin.sum_univ_two,
    polarTangentialComponent,transposeOperator_apply,planarPartMap,toPhysicalValue,operatorEntry,operatorMatrix,planarBasis,originalPlanarBasis]
  ring

theorem originalToroidalCovector_storage (seed derivative : ComplexEuclidean 2→L[ℂ]ComplexEuclidean 2)
    (length angle : ℝ) (point : ClosedDisk) (value : ComplexEuclidean 3) :
    (∑ coordinate : Fin 3,physicalGaugeCovector (operatorMatrix seed) ((length : ℂ)⁻¹ • operatorMatrix derivative) angle point 1 coordinate*value coordinate)=
      (toroidalPartMap (toPhysicalValue value)+(length⁻¹ : ℂ) •
        (point.val 0 • planarComponentMap 0 (transposeOperator derivative (planarPartMap (toPhysicalValue value)))+
         point.val 1 • planarComponentMap 1 (transposeOperator derivative (planarPartMap (toPhysicalValue value))))) 0 := by
  simp [physicalGaugeCovector,planarPhysicalInclusion,toroidalPhysicalColumn,spatialColumn,Matrix.mul_apply,
    Fin.sum_univ_three,Fin.sum_univ_two,transposeOperator_apply,planarPartMap,toroidalPartMap,toPhysicalValue,
    planarComponentMap,operatorEntry,operatorMatrix,planarBasis,originalPlanarBasis]
  ring

/-- The physical means supplied by the actual smooth constraint kernel are
exactly the two original gauge covector pairings. -/
theorem originalDomain_covectorMeans (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed∈Seed.parameterDomain) (vector : ACore parameters 3)
    (constrained : VectorConstraints parameters seed inside (toPhysicalCore parameters vector))
    (radius : ℝ) (bounded : |radius|≤1) (axialAngle : ℝ) (kind : Fin 2) :
    sourceAngularAverage (fun polarAngle =>
      ∑ coordinate : Fin 3,
        physicalGaugeCovector (physicalSeedMatrix (seed 0) (seed 1) (seed 2) (seed 3) axialAngle)
          ((parameters.length : ℂ)⁻¹ • operatorMatrix
            (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) axialAngle))
          polarAngle (polarClosedPoint radius bounded polarAngle) kind coordinate *
          coreValue vector (polarClosedPoint radius bounded polarAngle) axialAngle coordinate)=0 := by
  fin_cases kind
  · have mean := originalDomain_poloidalMean parameters seed inside vector constrained radius bounded axialAngle
    simp only [planarPartCore,coreValue_gaugeValueMap,toPhysicalCore,coreValue_valueMap] at mean
    refine Eq.trans ?_ mean
    apply congrArg sourceAngularAverage
    funext polarAngle
    convert originalPoloidalCovector_storage
        (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) axialAngle)
        ((parameters.length : ℂ)⁻¹ • deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) axialAngle)
        polarAngle (polarClosedPoint radius bounded polarAngle)
        (coreValue vector (polarClosedPoint radius bounded polarAngle) axialAngle) using 1
    simp [physicalSeedMatrix,operatorMatrix_smul]
  · have mean := originalDomain_toroidalMean parameters seed inside vector constrained radius bounded axialAngle
    simp only [planarPartCore,toroidalPartCore,coreValue_gaugeValueMap,toPhysicalCore,coreValue_valueMap] at mean
    refine Eq.trans ?_ mean
    apply congrArg sourceAngularAverage
    funext polarAngle
    exact originalToroidalCovector_storage
      (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) axialAngle)
      (deriv (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3)) axialAngle)
      parameters.length polarAngle (polarClosedPoint radius bounded polarAngle)
      (coreValue vector (polarClosedPoint radius bounded polarAngle) axialAngle)


end Grad.OriginalKernelCovariantRecovery
