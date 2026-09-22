import AKDM8ActualCovariantPureCellSolve
import AKAN3ActualJetExhaustionTwenty

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.FinitePhysicalJetLift
open Grad.ActualPuncturedFamily Grad.Constraints Grad.Q24Realization Grad.AxisSplit Grad.ChartAxisLift Grad.ConstrainedTransfer Grad.NonlinearQuotientBounds
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
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




open Grad.ActualScaledNativeCoefficients Grad.ActualCartesianDescent Grad.OriginalCartesianTameEstimate
open Grad.ActualCartesianWeakEquations Grad.ActualScalarWeakEquations Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.SourceBoundaryTrace Grad.ActualCartesianFlux Grad.ActualNativeCellMoments
open Grad.SourceCollarCoefficients Grad.CartesianStartup Grad.ActualSmoothPhysicalField Grad.ActualPuncturedReconstruction

/-- Exact original finite-jet residual, SAME recovered cores and actual
native/pure-cell twenty-loss bounds, with an independent base payment. -/
theorem actualFiniteJet_originalCovariant_cellTwenty
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length) :
    ∃ nativeConstant cellConstant : ℕ → ℝ, (∀ t, 0 ≤ nativeConstant t) ∧ (∀ t, 0 ≤ cellConstant t) ∧
      ∃ baseConstant : ℝ, 0 ≤ baseConstant ∧
      ∀ (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
        (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
        (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
        (base : RealJointCore parameters reference insideR)
        (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
        (compactNonnegative : 0 ≤ compact) (alphaSmall : |seed 1| ≤ compact)
        (deltaSmall : |seed 2| ≤ compact) (parameterSmall : |seed 3| ≤ compact)
        (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 8 ≤ actualJetExhaustionRadius parameters length compact)
        (_bounded : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 20 ≤ 1)
        (_startupSmall : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
          (seed 0) base.1 10 < actualNativeAllOrderRadius parameters length compact lengthPositive compactNonnegative)
        (source : OriginalFlatSource parameters length),
        let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
        let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
          compactNonnegative alphaSmall deltaSmall parameterSmall
        let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
        let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
        let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
    ∃ family : NativeCartesianFamily parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat,
      (∀ index grade, family.nativeNorm index grade ≤ nativeConstant grade *
        (‖quotientEta parameters (grade+20) source.val.val‖+
          physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+20)*‖quotientEta parameters 20 source.val.val‖)) ∧
      (∀ index, family.nativeNorm index 0 ≤ baseConstant*‖quotientEta parameters 20 source.val.val‖) ∧
    ∃ covariant : ACore parameters 3, ∃ xi scalar : ACore parameters 1,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ cell : ℤ,
        (covariant.val cell).value point=actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) cell point.val) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
          actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters xi).value (point,(axial : CellCircle))=
          actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
          actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state exSmall residual flat family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
            (fun index grade => ⟨family.graded index grade,family.inserted index grade⟩) (point.val,axial)) ∧
      ∀ grade, originalCellNorm parameters grade covariant ≤ cellConstant grade *
        (‖quotientEta parameters (grade+20) source.val.val‖+
          physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+20)*‖quotientEta parameters 20 source.val.val‖) := by
  let certificate := actualCartesianSource_covariantXiScalar_quantitative parameters length compact lengthPositive
  let nativeCost := certificate.choose
  let cellCost := certificate.choose_spec.choose
  have costLaws := certificate.choose_spec.choose_spec
  have nativeNonnegative := costLaws.1
  have cellNonnegative := costLaws.2.1
  have solve := costLaws.2.2
  let paymentCertificate := fun grade => actualFiniteSourceResidual_exhaustion_payment parameters length grade
  let paymentCost := fun grade => (paymentCertificate grade).choose
  have paymentNonnegative := fun grade => (paymentCertificate grade).choose_spec.1
  have paymentBound := fun grade => (paymentCertificate grade).choose_spec.2
  let lowCertificate := originalRealFiniteLiftResidual_low_payment parameters length
  let lowCost := lowCertificate.choose
  have lowNonnegative := lowCertificate.choose_spec.1
  have lowBound := lowCertificate.choose_spec.2
  refine ⟨(fun grade => nativeCost grade*paymentCost grade),
    (fun grade => cellCost grade*paymentCost grade),
    (fun grade => mul_nonneg (nativeNonnegative grade) (paymentNonnegative grade)),
    (fun grade => mul_nonneg (cellNonnegative grade) (paymentNonnegative grade)),
    (2*nativeCost 0)*lowCost,
    mul_nonneg (mul_nonneg (by norm_num) (nativeNonnegative 0)) lowNonnegative,?_⟩
  intro widthHalf widthLength reference insideR seed insideS base axis compactNonnegative alphaSmall deltaSmall parameterSmall small bounded startupSmall source
  dsimp only
  let field := actualFiniteCurrentField parameters reference insideR seed insideS base
  let low := actualJetExhaustion_cubicSmall parameters length compact reference insideR seed insideS base small
  let state := actualJetExhaustionState parameters length compact reference insideR seed insideS base small
    compactNonnegative alphaSmall deltaSmall parameterSmall
  let exSmall := actualJetExhaustion_exSmall parameters length compact reference insideR seed insideS base small
  let residual := actualFiniteSourceResidual parameters length (seed 0) reference insideR seed insideS base low source
  let flat := actualFiniteSourceResidual_isFlat parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
  have vanishing := actualFiniteSourceResidual_higherVanishing parameters length (seed 0) lengthPositive reference insideR seed insideS base low axis source
  have stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ 1 :=
    (physicalBudget_monotone parameters field (seed 0) base.1 (by norm_num : 14≤20)).trans bounded
  let solved := solve widthHalf widthLength state exSmall stateBound residual flat vanishing startupSmall
  let family := solved.choose
  have native := solved.choose_spec.1
  have baseBound := solved.choose_spec.2.1
  let coreResult := solved.choose_spec.2.2
  let covariant := coreResult.choose
  let xi := coreResult.choose_spec.choose
  let scalar := coreResult.choose_spec.choose_spec.choose
  have identities := coreResult.choose_spec.choose_spec.choose_spec
  have covariantCells := identities.1
  have covariantSame := identities.2.1
  have xiSame := identities.2.2.1
  have scalarSame := identities.2.2.2.1
  have cellBound := identities.2.2.2.2
  have payment (grade : ℕ) :
      ‖quotientEta parameters (grade+8) residual‖+
        physicalBudget parameters field (seed 0) base.1 (grade+14)*‖quotientEta parameters 8 residual‖ ≤
      paymentCost grade*(‖quotientEta parameters (grade+20) source.val.val‖+
        physicalBudget parameters field (seed 0) base.1 (grade+20)*‖quotientEta parameters 20 source.val.val‖) := by
    have increased := mul_le_mul_of_nonneg_right
      (physicalBudget_monotone parameters field (seed 0) base.1 (by omega : grade+14≤grade+20))
      (norm_nonneg (quotientEta parameters 8 residual))
    have bound := paymentBound grade (seed 0) base.1 field low bounded
      (actualFiniteCurrentScalar parameters reference insideR seed insideS base) source.val.val
    exact (add_le_add (le_refl (‖quotientEta parameters (grade+8) residual‖)) increased).trans bound
  refine ⟨family,?_,?_,covariant,xi,scalar,covariantCells,covariantSame,xiSame,scalarSame,?_⟩
  · intro index grade
    exact (native index grade).trans ((mul_le_mul_of_nonneg_left (payment grade) (nativeNonnegative grade)).trans_eq
      (mul_assoc _ _ _).symm)
  · intro index
    have residualLow := lowBound (seed 0) base.1 field low bounded
      (actualFiniteCurrentScalar parameters reference insideR seed insideS base) source.val.val
    change ‖quotientEta parameters 8 residual‖ ≤ lowCost*‖quotientEta parameters 20 source.val.val‖ at residualLow
    exact (baseBound index).trans ((mul_le_mul_of_nonneg_left residualLow
      (mul_nonneg (by norm_num) (nativeNonnegative 0))).trans_eq (mul_assoc _ _ _).symm)
  · intro grade
    exact (cellBound grade).trans ((mul_le_mul_of_nonneg_left (payment grade) (cellNonnegative grade)).trans_eq
      (mul_assoc _ _ _).symm)

end Grad.FinitePhysicalJetLift
