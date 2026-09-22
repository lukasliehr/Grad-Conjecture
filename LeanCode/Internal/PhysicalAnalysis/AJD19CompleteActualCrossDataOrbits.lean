import AJD16ActualCrossBulkOperatorOrbits
import AJD18SameLowToHighBoundaryOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularCrossMaps Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularHighInverseOrbit
open Grad.AnnularLowOrbit Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.AnnularKernelL2
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

section PiOperators
variable {Index X E P : Type*} [Fintype Index]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup E] [NormedSpace ℂ E]

def piOperatorLinear : (Index → X →L[ℂ] E) →ₗ[ℂ] (X →L[ℂ] Index → E) where
  toFun := ContinuousLinearMap.pi
  map_add' first second := by apply ContinuousLinearMap.ext; intro field; rfl
  map_smul' scalar family := by apply ContinuousLinearMap.ext; intro field; rfl

def piOperatorCLM : (Index → X →L[ℂ] E) →L[ℂ] (X →L[ℂ] Index → E) :=
  piOperatorLinear.mkContinuous 1 (fun family => by
    rw [one_mul]
    exact ContinuousLinearMap.norm_pi_le_of_le (norm_le_pi_norm family) (norm_nonneg family))

def piLpOperator (family : Index → X →L[ℂ] E) : X →L[ℂ] PiLp 2 (fun _ : Index => E) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Index => E)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi family)

variable [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem piLpOperator_contDiff (family : Index → P → X →L[ℂ] E)
    (smooth : ∀ index, ContDiff ℝ ∞ (family index)) :
    ContDiff ℝ ∞ (fun point => piLpOperator (fun index => family index point)) := by
  have all : ContDiff ℝ ∞ (fun point index => family index point) := contDiff_pi.mpr smooth
  have assembled := ((piOperatorCLM (Index := Index) (X := X) (E := E)).restrictScalars ℝ).contDiff.comp all
  exact complexOperatorComposition_contDiff _ _ contDiff_const assembled
end PiOperators

attribute [local instance] Grad.AnnularCrossOrbit.crossDataNormed Grad.AnnularCrossOrbit.crossDataSeminormed
  Grad.AnnularCrossOrbit.crossDataRealInner Grad.AnnularCrossOrbit.crossDataRealNormed Grad.AnnularCrossOrbit.crossDataRealModule
  Grad.AnnularCrossOrbit.crossHighNormed Grad.AnnularCrossOrbit.crossHighSeminormed
  Grad.AnnularCrossOrbit.crossHighComplexNormed Grad.AnnularCrossOrbit.crossHighComplexModule
  Grad.AnnularCrossOrbit.crossHighRealNormed Grad.AnnularCrossOrbit.crossHighRealModule

local instance lowToHighOperatorRealNormed (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) :
    NormedSpace ℝ (lowEnergyGraph lower L positive →L[ℂ] CrossHighData parameters lower) :=
  NormedSpace.restrictScalars ℝ ℂ (lowEnergyGraph lower L positive →L[ℂ] CrossHighData parameters lower)
local instance highToLowOperatorRealNormed (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L) :
    NormedSpace ℝ (CrossHighSpace lower L positive lengthPositive →L[ℂ] LowEnergyData lower) :=
  NormedSpace.restrictScalars ℝ ℂ (CrossHighSpace lower L positive lengthPositive →L[ℂ] LowEnergyData lower)

variable (parameters : PhaseParameters) (L compact lower : ℝ) (lengthPositive : 0 < L)
  (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (state : RetainedInverseState parameters L compact)

def lowToHighCrossOrbit (tau : OrbitParameter) :
    lowEnergyGraph lower L positive →L[ℂ] CrossHighData parameters lower :=
  hilbertOperatorPair
    (piLpOperator (fun row : Fin 3 => lowToHighBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state row tau))
    (lowToHighBoundaryOrbit parameters L compact lower lengthPositive positive lowerHalf state tau)

theorem lowToHighCrossOrbit_contDiff :
    ContDiff ℝ ∞ (lowToHighCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state) :=
  hilbertOperatorPair_contDiff _ _
    (piLpOperator_contDiff _ (fun row => lowToHighBulkOrbit_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state row))
    (lowToHighBoundaryOrbit_contDiff parameters L compact lower lengthPositive positive lowerHalf state)

/-- Both data blocks are the exact conjugation of the original BF16 cross datum. -/
theorem lowToHighCrossOrbit_apply (tau : OrbitParameter) (field : lowEnergyGraph lower L positive) :
    lowToHighCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state tau field =
      crossDataTranslation parameters lower tau
        (lowToHighCross parameters lower L compact lengthPositive positive lowerHalf state
          (lowTranslation lower L positive (-tau) field)) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (CrossHighBulk lower) (HighBoundaryPrimitive parameters 0 0)).injective
  apply Prod.ext
  · apply PiLp.ext
    intro row
    exact lowToHighBulkOrbit_apply parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state row tau field
  · rfl

def highToLowCrossOrbit (tau : OrbitParameter) :
    CrossHighSpace lower L positive lengthPositive →L[ℂ] LowEnergyData lower :=
  hilbertOperatorPair
    (highToLowBulkOrbit parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state tau) 0

theorem highToLowCrossOrbit_contDiff :
    ContDiff ℝ ∞ (highToLowCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state) :=
  hilbertOperatorPair_contDiff _ _
    (highToLowBulkOrbit_contDiff parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state) contDiff_const

/-- The zero incoming coordinate is preserved along the SAME original BF18 source orbit. -/
theorem highToLowCrossOrbit_apply (tau : OrbitParameter) (field : CrossHighSpace lower L positive lengthPositive) :
    highToLowCrossOrbit parameters L compact lower lengthPositive positive lowerHalf state tau field =
      lowDataTranslationEquivalence lower tau
        (highToLowCross parameters lower L compact lengthPositive positive (lowerHalf.trans (by norm_num)) state
          (highTranslationEquivalence lower L positive lengthPositive (-tau) field)) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
  apply Prod.ext
  · exact highToLowBulkOrbit_apply parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state tau field
  · exact (map_zero (lowBoundaryTranslation tau)).symm

end Grad.AnnularCrossOrbit
