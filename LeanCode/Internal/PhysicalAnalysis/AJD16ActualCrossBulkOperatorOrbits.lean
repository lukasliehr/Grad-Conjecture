import AJD14SameCompleteHighCrossResponseOrbit
import AJD15OriginalHighCrossInputCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2 Grad.AnnularLowCompletion

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (bounded : lower ≤ 1) (lengthPositive : 0 < L) (state : RetainedInverseState parameters L compact)

theorem actualLowRowOrbit_contDiff (row : Fin 3) :
    ContDiff ℝ ∞ (actualLowRowOrbit parameters L compact lower positive bounded state row) := by
  let jet := fun angular cell tau => actualLowRowOrbitJet parameters L compact lower positive bounded state row tau angular cell
  have derivative (angular cell : ℕ) (tau : OrbitParameter) :
      HasFDerivAt (jet angular cell) (orbitColumns (jet (angular + 1) cell tau) (jet angular (cell + 1) tau)) tau :=
    radialOrbitJetAction_hasFDerivAt parameters (lowPhysicalRowKernel parameters L compact state row)
      (lowPhysicalRowKernel_regular parameters L compact state row) 0 lower positive bounded tau angular cell
  have smooth := orbitTower_contDiff jet derivative 0 0
  have same : jet 0 0 = actualLowRowOrbit parameters L compact lower positive bounded state row := by
    funext tau
    exact radialOrbitJetAction_zero parameters (lowPhysicalRowKernel parameters L compact state row)
      (lowPhysicalRowKernel_regular parameters L compact state row) 0 lower positive bounded tau
  rw [same] at smooth
  exact smooth

def lowToHighBulkOrbit (row : Fin 3) (tau : OrbitParameter) :
    lowEnergyGraph lower L positive →L[ℂ] AnnularBulk lower :=
  (crossHighRestriction lower).comp
    ((actualLowRowOrbit parameters L compact lower positive bounded state row tau).comp
      ((lowNormalizedSevenInput parameters lower L lengthPositive positive).comp
        (lowStoredCoordinate lower L positive 0)))

theorem lowToHighBulkOrbit_contDiff (row : Fin 3) :
    ContDiff ℝ ∞ (lowToHighBulkOrbit parameters L compact lower positive bounded lengthPositive state row) :=
  complexOperatorComposition_contDiff _ _ contDiff_const
    (complexOperatorComposition_contDiff _ _
      (actualLowRowOrbit_contDiff parameters L compact lower positive bounded state row) contDiff_const)

theorem crossHighRestriction_translation (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    crossHighRestriction lower (orbitLpAction (RadialL2 1 lower) tau field) =
      highBulkTranslation lower tau (crossHighRestriction lower field) := by
  apply lp.ext
  funext mode
  rfl

/-- The same low-to-high physical rows, with their original seven rho-weighted inputs. -/
theorem lowToHighBulkOrbit_apply (row : Fin 3) (tau : OrbitParameter) (field : lowEnergyGraph lower L positive) :
    lowToHighBulkOrbit parameters L compact lower positive bounded lengthPositive state row tau field =
      highBulkTranslation lower tau
        (lowToHighBulkCross parameters lower L compact lengthPositive positive bounded state row
          (lowTranslation lower L positive (-tau) field)) := by
  unfold lowToHighBulkOrbit lowToHighBulkCross
  rw [actualLowRowOrbit_conjugation]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← lowNormalizedSevenInput_translation, crossHighRestriction_translation]
  rfl

def highToLowBulkOrbit (tau : OrbitParameter) :
    CrossHighSpace lower L positive lengthPositive →L[ℂ] LowEnergyBulk lower :=
  ((lowFirstOutput parameters lower L).comp (actualLowRowOrbit parameters L compact lower positive bounded state 0 tau) +
    (lowCellOutput lower L positive).comp (actualLowRowOrbit parameters L compact lower positive bounded state 1 tau) +
    (lowAngularOutput lower L positive).comp (actualLowRowOrbit parameters L compact lower positive bounded state 2 tau)).comp
    (highCrossSevenInput lower L positive lengthPositive)

theorem highToLowBulkOrbit_contDiff :
    ContDiff ℝ ∞ (highToLowBulkOrbit parameters L compact lower positive bounded lengthPositive state) :=
  complexOperatorComposition_contDiff _ _
    (((complexOperatorComposition_contDiff _ _ contDiff_const
      (actualLowRowOrbit_contDiff parameters L compact lower positive bounded state 0)).add
      (complexOperatorComposition_contDiff _ _ contDiff_const
        (actualLowRowOrbit_contDiff parameters L compact lower positive bounded state 1))).add
      (complexOperatorComposition_contDiff _ _ contDiff_const
        (actualLowRowOrbit_contDiff parameters L compact lower positive bounded state 2))) contDiff_const

/-- The same high-to-low source, including all three original normalized outputs. -/
theorem highToLowBulkOrbit_apply (tau : OrbitParameter) (field : CrossHighSpace lower L positive lengthPositive) :
    highToLowBulkOrbit parameters L compact lower positive bounded lengthPositive state tau field =
      lowBulkTranslation lower tau
        (highToLowBulkCross parameters lower L compact lengthPositive positive bounded state
          (highTranslationEquivalence lower L positive lengthPositive (-tau) field)) := by
  unfold highToLowBulkOrbit highToLowBulkCross
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add, actualLowRowOrbit_conjugation,
    ← highCrossSevenInput_covariant lower L positive lengthPositive (-tau) field, lowFirstOutput_translation, lowCellOutput_translation, lowAngularOutput_translation]

end Grad.AnnularCrossOrbit
