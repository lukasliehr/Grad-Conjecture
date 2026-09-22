import AKP11FullFamilyNativeCompatibility
import AKT8ActualPuncturedPhysicalPressureAndScalar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule





open Grad.SourceCollarCoefficients Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower) (cofinal : Tendsto lower atTop (𝓝 0))
    (field : ∀ index, OriginalFiveBlockAmbient parameters (lower index) length (positive index))
    (graded : ∀ index (_t : ℕ), CoupledSpace (lower index) length (positive index) lengthPositive)
    (inserted : ∀ index t, CoupledInsertedGrade (lower index) length (positive index) lengthPositive t
      (originalWeightedRetainedObservation parameters (lower index) length (positive index) (bounded index).le lengthPositive (field index))
      (graded index t))
    (compatible : ∀ first second (included : lower first ≤ lower second),
      originalFiveBlockRestriction parameters (lower first) (lower second) length (positive first) (positive second)
        (bounded second) lengthPositive included (field first) = field second)

/-- The punctured physical field comes from the SAME actual full original
family, rather than independently selecting each frequency or grade. -/
def originalFamilyPhysicalPair (grade : ℕ) : ℝ → CellL2 1 × CellL2 1 :=
  puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal
    (fun index => originalWeightedRetainedObservation parameters (lower index) length (positive index) (bounded index).le lengthPositive (field index))
    (fun index t => ⟨graded index t,inserted index t⟩) grade

include compatible decreasing

theorem originalFamilyPhysicalPair_continuous (grade : ℕ) :
    ContinuousOn (originalFamilyPhysicalPair parameters length lengthPositive lower positive bounded cofinal field graded inserted grade)
      (Ioc (0 : ℝ) 1) :=
  puncturedPhysicalPair_continuous parameters length lengthPositive lower positive bounded decreasing cofinal _ _
    (fullOriginalFamily_nativeCompatible parameters length lengthPositive lower positive bounded decreasing field compatible) grade

theorem originalFamilyPhysicalPair_same (grade index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (lower index) 1) (mode : ℤ × ℤ) :
    ((originalFamilyPhysicalPair parameters length lengthPositive lower positive bounded cofinal field graded inserted grade radius).1 mode,
     (originalFamilyPhysicalPair parameters length lengthPositive lower positive bounded cofinal field graded inserted grade radius).2 mode) =
    (sameCoupledXCoefficient parameters (lower index) length (positive index) (bounded index) lengthPositive
      (originalWeightedRetainedObservation parameters (lower index) length (positive index) (bounded index).le lengthPositive (field index))
      grade ⟨radius,inside⟩ mode,
     sameCoupledXiCoefficient parameters (lower index) length (positive index) (bounded index) lengthPositive
      (originalWeightedRetainedObservation parameters (lower index) length (positive index) (bounded index).le lengthPositive (field index))
      grade ⟨radius,inside⟩ mode) :=
  puncturedPhysicalPair_physical parameters length lengthPositive lower positive bounded decreasing cofinal _ _
    (fullOriginalFamily_nativeCompatible parameters length lengthPositive lower positive bounded decreasing field compatible) grade index radius inside mode

end Grad.ActualPuncturedFamily
