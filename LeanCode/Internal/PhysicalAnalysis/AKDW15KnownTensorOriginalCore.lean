import AKDW14FixedOriginalCoreNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupSpatialAction

def knownForceTensor (rank : ℕ) (outer inner : Fin 2) : StartupSpatialAction rank 2 3 1 1 :=
  ((principalFixed rank outer inner 0).comp (value rank planarInclusionMap)).smul (-1) |>.add
    ((((principalFixed rank outer inner 2).comp (value rank planarInclusionMap)).comp
      ((value rank quarterValueMap).comp (average rank))).smul (1/2))

def knownThirdTensor (rank : ℕ) (outer inner : Fin 2) : StartupSpatialAction rank 1 3 1 1 :=
  (principalFixed rank outer inner 1).comp (value rank toroidalInclusionMap)

theorem knownForceTensor_controlled (parameters : PhaseParameters) (rank : ℕ) (outer inner : Fin 2) :
    (knownForceTensor rank outer inner).OriginalEndpointControlled parameters :=
  (((principalFixed_originalEndpointControlled parameters rank outer inner 0).comp
    (value_originalEndpointControlled parameters rank planarInclusionMap)).smul (-1)).add
    ((((principalFixed_originalEndpointControlled parameters rank outer inner 2).comp
      (value_originalEndpointControlled parameters rank planarInclusionMap)).comp
      ((value_originalEndpointControlled parameters rank quarterValueMap).comp
        (average_originalEndpointControlled parameters rank))).smul (1/2))

theorem knownThirdTensor_controlled (parameters : PhaseParameters) (rank : ℕ) (outer inner : Fin 2) :
    (knownThirdTensor rank outer inner).OriginalEndpointControlled parameters :=
  (principalFixed_originalEndpointControlled parameters rank outer inner 1).comp
    (value_originalEndpointControlled parameters rank toroidalInclusionMap)

end StartupSpatialAction

theorem startupKnownTensor_fixedFormula (rank : ℕ) (force : StartupL2 2) (third : StartupL2 1) (outer inner : Fin 2) :
    startupThreeRowTensor (-force) third (startupERSourceFlux force) outer inner=
      (StartupSpatialAction.knownForceTensor rank outer inner).signed.coarse force+
      (StartupSpatialAction.knownThirdTensor rank outer inner).signed.coarse third := by
  have firstSame : (StartupSpatialAction.knownForceTensor rank outer inner).signed.coarse force=
      (-1 : ℂ) • startupPrincipalFixedKernel outer inner 0 (originalValueKernel planarInclusionMap force)+
      (1/2 : ℂ) • startupPrincipalFixedKernel outer inner 2
        (originalValueKernel planarInclusionMap (originalValueKernel quarterValueMap (originalAverageKernel force))) := by
    change (-1 : ℂ) • (StartupSpatialAction.principalFixed (L:=1) (ell:=1) rank outer inner 0).signed.coarse
      (originalValueKernel planarInclusionMap force)+(1/2 : ℂ) •
      (StartupSpatialAction.principalFixed (L:=1) (ell:=1) rank outer inner 2).signed.coarse
        (originalValueKernel planarInclusionMap (originalValueKernel quarterValueMap (originalAverageKernel force)))=_
    rw [StartupSpatialAction.principalFixed_coarse,StartupSpatialAction.principalFixed_coarse]
  have secondSame : (StartupSpatialAction.knownThirdTensor rank outer inner).signed.coarse third=
      startupPrincipalFixedKernel outer inner 1 (originalValueKernel toroidalInclusionMap third) := by
    change (StartupSpatialAction.principalFixed (L:=1) (ell:=1) rank outer inner 1).signed.coarse
      (originalValueKernel toroidalInclusionMap third)=_
    rw [StartupSpatialAction.principalFixed_coarse]
  rw [firstSame,secondSame]
  unfold startupThreeRowTensor
  rw [Fin.sum_univ_three]
  change startupPrincipalFixedKernel outer inner 0 (originalValueKernel planarInclusionMap (-force))+
    startupPrincipalFixedKernel outer inner 1 (originalValueKernel toroidalInclusionMap third)+
    startupPrincipalFixedKernel outer inner 2 (originalValueKernel planarInclusionMap (startupERSourceFlux force))=
    ((-1 : ℂ) • startupPrincipalFixedKernel outer inner 0 (originalValueKernel planarInclusionMap force)+
      (1/2 : ℂ) • startupPrincipalFixedKernel outer inner 2
        (originalValueKernel planarInclusionMap (originalValueKernel quarterValueMap (originalAverageKernel force))))+
    startupPrincipalFixedKernel outer inner 1 (originalValueKernel toroidalInclusionMap third)
  simp only [startupERSourceFlux,map_neg,map_smul,neg_one_smul]
  abel

/-- The actual known ER tensor is an original core at the same width. -/
theorem startupKnownTensor_core_exists (parameters : PhaseParameters) (force : ACore parameters 2)
    (third : ACore parameters 1) (outer inner : Fin 2) :
    ∃ image : ACore parameters 3,originalSourceFieldLinear parameters image=
      startupThreeRowTensor (-originalSourceFieldLinear parameters force) (originalSourceFieldLinear parameters third)
        (startupERSourceFlux (originalSourceFieldLinear parameters force)) outer inner := by
  obtain ⟨first,firstSame⟩ := StartupSpatialAction.fixedCore_exists parameters _
    (StartupSpatialAction.knownForceTensor_controlled parameters 0 outer inner) force
  obtain ⟨second,secondSame⟩ := StartupSpatialAction.fixedCore_exists parameters _
    (StartupSpatialAction.knownThirdTensor_controlled parameters 0 outer inner) third
  refine ⟨first+second,?_⟩
  rw [map_add,firstSame,secondSame,startupKnownTensor_fixedFormula 0]

/-- Known tensor payment uses only the SAME force/third source norms. -/
theorem startupKnownTensor_core_bound (parameters : PhaseParameters) (rank : ℕ) (outer inner : Fin 2) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (force : ACore parameters 2) (third : ACore parameters 1) (image : ACore parameters 3),
      originalSourceFieldLinear parameters image=
        startupThreeRowTensor (-originalSourceFieldLinear parameters force) (originalSourceFieldLinear parameters third)
          (startupERSourceFlux (originalSourceFieldLinear parameters force)) outer inner →
      originalGradeNorm rank image≤constant*(originalGradeNorm rank force+originalGradeNorm rank third) := by
  obtain ⟨firstCost,firstNonnegative,firstBound⟩ := StartupSpatialAction.fixedCore_bound parameters _
    (StartupSpatialAction.knownForceTensor_controlled parameters rank outer inner)
  obtain ⟨secondCost,secondNonnegative,secondBound⟩ := StartupSpatialAction.fixedCore_bound parameters _
    (StartupSpatialAction.knownThirdTensor_controlled parameters rank outer inner)
  refine ⟨firstCost+secondCost,add_nonneg firstNonnegative secondNonnegative,?_⟩
  intro force third image same
  obtain ⟨first,firstSame⟩ := StartupSpatialAction.fixedCore_exists parameters _
    (StartupSpatialAction.knownForceTensor_controlled parameters rank outer inner) force
  obtain ⟨second,secondSame⟩ := StartupSpatialAction.fixedCore_exists parameters _
    (StartupSpatialAction.knownThirdTensor_controlled parameters rank outer inner) third
  have identical : image=first+second := by
    apply originalSourceFieldLinear_injective parameters
    rw [map_add,firstSame,secondSame,same,startupKnownTensor_fixedFormula rank]
  rw [identical]
  have paid := (originalGradeNorm_add_le rank first second).trans
    (add_le_add (firstBound force first firstSame) (secondBound third second secondSame))
  nlinarith [mul_nonneg firstNonnegative (originalGradeNorm_nonnegative rank third),
    mul_nonneg secondNonnegative (originalGradeNorm_nonnegative rank force)]

end Grad.CartesianStartup
