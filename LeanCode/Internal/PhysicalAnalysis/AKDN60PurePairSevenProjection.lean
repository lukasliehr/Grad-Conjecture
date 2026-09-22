import AKDN56PureBalancedPairEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryLift Grad.AnnularReconstruction Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.Ledger Grad.AnnularGeneralSourceRegularity

def nativeSevenSlotProjection (parameters : PhaseParameters) (slot : Fin 7) : CellL2 7 →L[ℂ] CellL2 1 :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit (0 : Fin 1) slot)
    (norm_nonneg _) (fun _ => le_rfl)

/-- One extra pure frequency grade permits fixed bounded recovery from
slots 3 and 0 of the original seven packet. No coefficient is introduced. -/
def nativeBalancedSevenProjection (parameters : PhaseParameters) : CellL2 7 →L[ℂ] PhysicalHilbertPair :=
  (nativeSevenSlotProjection parameters 3).prod
    ((hilbertFrequencyOperator parameters 1 none).comp (nativeSevenSlotProjection parameters 0))

theorem nativeSevenSlotProjection_injection (parameters : PhaseParameters) (slot input : Fin 7)
    (value : CellL2 1) :
    nativeSevenSlotProjection parameters slot (hilbertSlotInjection parameters input value) =
      if slot=input then value else 0 := by
  apply lp.ext
  funext mode
  change matrixUnit (0 : Fin 1) slot (matrixUnit input (0 : Fin 1) (value mode)) = _
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  split_ifs with same
  · subst input
    simp [matrixUnit_apply,operatorBasis]
  · simp [matrixUnit_apply,operatorBasis,same]

theorem nativeSevenSlotProjection_balanced (parameters : PhaseParameters) (radius : ℝ)
    (field : PhysicalHilbertPair) :
    nativeSevenSlotProjection parameters 3 (balancedSevenInput parameters radius field) =
      hilbertFrequencyOperator parameters 1 none field.1 ∧
    nativeSevenSlotProjection parameters 0 (balancedSevenInput parameters radius field) = field.2 := by
  have expanded : balancedSevenInput parameters radius field =
      ((hilbertSlotInjection parameters 0 field.2+
        hilbertSlotInjection parameters 1 (hilbertFrequencyOperator parameters 1 (some false) field.1))+
        (radius : ℂ) • hilbertSlotInjection parameters 2 (hilbertFrequencyOperator parameters 1 (some true) field.1))+
        hilbertSlotInjection parameters 3 (hilbertFrequencyOperator parameters 1 none field.1) := rfl
  rw [expanded]
  constructor <;> simp only [map_add,map_smul,nativeSevenSlotProjection_injection]
  · norm_num [Fin.ext_iff]
  · norm_num [Fin.ext_iff]

theorem nativeBalancedSevenProjection_recovers (parameters : PhaseParameters) (radius : ℝ)
    (high low : PhysicalHilbertPair)
    (same : ∀ mode, hilbertPairCoefficient mode high =
      (annularFrequency mode.1 mode.2 : ℂ) • hilbertPairCoefficient mode low) :
    nativeBalancedSevenProjection parameters (balancedSevenInput parameters radius high) = low := by
  have projection := nativeSevenSlotProjection_balanced parameters radius high
  change (nativeSevenSlotProjection parameters 3 (balancedSevenInput parameters radius high),
    hilbertFrequencyOperator parameters 1 none (nativeSevenSlotProjection parameters 0 (balancedSevenInput parameters radius high)))=low
  rw [projection.1,projection.2]
  apply Prod.ext <;> apply lp.ext <;> funext mode
  · rw [hilbertFrequencyOperator_apply]
    have shift := congrArg Prod.fst (same mode)
    change high.1 mode=(annularFrequency mode.1 mode.2 : ℂ) • low.1 mode at shift
    rw [shift]
    simp only [frequencyRatioSymbol,one_div]
    change (annularFrequency mode.1 mode.2 : ℂ)⁻¹ • ((annularFrequency mode.1 mode.2 : ℂ) • low.1 mode)=_
    exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (annularFrequency_pos mode).ne') _
  · rw [hilbertFrequencyOperator_apply]
    have shift := congrArg Prod.snd (same mode)
    change high.2 mode=(annularFrequency mode.1 mode.2 : ℂ) • low.2 mode at shift
    rw [shift]
    simp only [frequencyRatioSymbol,one_div]
    change (annularFrequency mode.1 mode.2 : ℂ)⁻¹ • ((annularFrequency mode.1 mode.2 : ℂ) • low.2 mode)=_
    exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (annularFrequency_pos mode).ne') _

theorem nativeBalancedSevenProjection_known (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (source : Grad.QuotientProjection.SmoothQuotient parameters)
    (grade : ℕ) (radius : ℝ) :
    nativeBalancedSevenProjection parameters
      (actualCartesianKnownSevenCurve parameters length lower positive bounded source grade radius)=0 := by
  unfold actualCartesianKnownSevenCurve
  change (nativeSevenSlotProjection parameters 3 _,hilbertFrequencyOperator parameters 1 none (nativeSevenSlotProjection parameters 0 _))=0
  simp only [map_add,nativeSevenSlotProjection_injection]
  norm_num [Fin.ext_iff]

end Grad.OriginalCartesianTameEstimate
