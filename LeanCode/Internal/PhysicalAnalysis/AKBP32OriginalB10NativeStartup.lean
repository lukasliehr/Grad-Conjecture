import AKBP31SameNativeRowsH1

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.CartesianState Grad.CartesianUncompressed Grad.AnalyticWeights.Calculus Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

/-- One original B10 neighborhood, fixed before ell, data and the unknown,
supplies the actual tensor resolvents and native same-field H1 startup. The
three remaining coefficient equalities are literal realization identities,
not PDE or regularity assumptions. -/
theorem startupOriginalB10_native_h1 (parameters : PhaseParameters)
    (L radius primitiveThreshold : ℝ) (positive : 0 < L) (radiusNonnegative : 0 ≤ radius)
    (primitivePositive : 0 < primitiveThreshold)
    (outer inside : Spatial → ℝ) (outerSmooth : ContDiff ℝ ∞ outer) (insideSmooth : ContDiff ℝ ∞ inside)
    (outerCompact : HasCompactSupport outer) (insideCompact : HasCompactSupport inside)
    (outerDisk : tsupport outer ⊆ openUnitDisk) (insideDisk : tsupport inside ⊆ openUnitDisk)
    (plateau : Set.EqOn outer (fun _ => 1) (tsupport inside))
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → inside first = inside second) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∀ (ell rho alpha delta parameter epsilon : ℝ)
        (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
        |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
        ∀ base : ACore parameters 3, physicalBudget parameters base rho epsilon 10 < lowRadius →
          ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
            primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ primitiveThreshold ∧
            ∃ inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation),
              ActualLedgerReduction ledger inverseCoherent ∧
              ∀ (_gammaNonnegative : 0 ≤ parameters.gamma) (_ellNonnegative : 0 ≤ ell) (_ellOne : ell ≤ 1)
                (rows rawRows : StartupNativeERRows) (psi : StartupL2 1),
                StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma ell) rows rawRows →
                StartupNativeWeakRows (ell/L) psi rawRows →
                ∀ (forceFirst : StartupFirst 2) (thirdFirst : StartupFirst 1),
                  Grad.WeightedJets.base 2 1 openUnitDisk (fun _ => 0) forceFirst = rows.knownForce.field →
                  Grad.WeightedJets.base 1 1 openUnitDisk (fun _ => 0) thirdFirst = rows.knownThird.field →
                  startupGenuineForceKernel admissible ledger.val ledger.property.1 inverseCoherent rows.circle.field = rows.forceCorrection.field →
                  originalThirdCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent rows.circle.field = rows.thirdCorrection.field →
                  startupGenuinePrincipalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent rows.circle.field = rows.currentFlux.field →
                  ∃ improved : FieldH1, valueInclusion improved =
                    startupPlaneExtension (startupCutoffL2 inside insideSmooth insideCompact rows.circle.field) := by
  obtain ⟨lowRadius,lowPositive,lowOne,provider⟩ := actualOriginalB10GenuinePrincipalResolventSmall parameters
    L radius primitiveThreshold 1 positive radiusNonnegative primitivePositive zero_lt_one outer outerSmooth outerCompact outerDisk
  refine ⟨lowRadius,lowPositive,lowOne,?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall original low
  obtain ⟨ledger,primitive,inverseCoherent,reduction,regular,compatible,coarseSmall,fineSmall⟩ :=
    provider ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall original low
  refine ⟨ledger,primitive,inverseCoherent,reduction,?_⟩
  intro gammaNonnegative ellNonnegative ellOne rows rawRows psi phase weak forceFirst thirdFirst forceBase thirdBase forceSame thirdSame fluxSame
  exact startupSame_nativeRows_h1 admissible ledger.val ledger.property.1 inverseCoherent gammaNonnegative ellNonnegative ellOne
    outer inside outerSmooth insideSmooth outerCompact insideCompact insideDisk plateau radial regular compatible coarseSmall fineSmall
    rows rawRows psi phase weak forceFirst thirdFirst forceBase thirdBase forceSame thirdSame fluxSame

end Grad.CartesianStartup
