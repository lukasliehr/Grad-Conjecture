import Q24TransferFamily
import Q24CoefficientFieldCalculus
import Q23SeedScalarFamilies

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisCore Grad.ImplementationReadiness
open Grad.SmoothingFamily

def movingChartDomain (parameters : PhaseParameters) (grade : ℕ) :
    Set (Seed.Parameters × XAmbient parameters grade) :=
  {pair | pair.1 ∈ Seed.parameterDomain ∧ pair.2 ∈ chartDomain parameters grade}

theorem movingChartDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (movingChartDomain parameters grade) :=
  (Seed.parameterDomain_isOpen.preimage continuous_fst).inter
    ((chartDomain_isOpen parameters grade).preimage continuous_snd)

/-- Literal Q18 with both the seed and completed original state varying. -/
def completedChartFamily (parameters : PhaseParameters) (grade : ℕ)
    (pair : Seed.Parameters × XAmbient parameters grade) :
    AGrade parameters 3 grade × AGrade parameters 1 grade :=
  (completedCoefficientField parameters 3 grade
      (completedTameSeedFieldFamily parameters grade pair.1)
      (completedRootFactor parameters grade pair.2.ofLp.1) +
    fieldValueMap parameters grade tameTangentInclusion
      (coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 0)
          (tangentComponentMap parameters grade 0 pair.2.ofLp.1) +
        coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 1)
          (tangentComponentMap parameters grade 1 pair.2.ofLp.1)) + pair.2.ofLp.2.ofLp.1,
    completedTameSeedScalarFamily parameters grade pair.1 + pair.2.ofLp.2.ofLp.2)

theorem completedChartFamily_contDiffOn (parameters : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedChartFamily parameters grade) (movingChartDomain parameters grade) := by
  have seedField : ContDiffOn ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade => completedTameSeedFieldFamily parameters grade pair.1)
      (movingChartDomain parameters grade) :=
    (completedTameSeedFieldFamily_contDiffOn parameters grade).comp contDiff_fst.contDiffOn
      (fun _ inside => inside.1)
  have seedOperators : ContDiffOn ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade =>
        completedCoefficientField parameters 3 grade (completedTameSeedFieldFamily parameters grade pair.1))
      (movingChartDomain parameters grade) :=
    completedCoefficientField_smooth parameters grade _ _ seedField
  have axes : ContDiff ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade => pair.2.ofLp.1) :=
    (stateAxis_contDiff parameters grade).comp contDiff_snd
  have fields : ContDiff ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade => pair.2.ofLp.2.ofLp) :=
    (stateFields_contDiff parameters grade).comp contDiff_snd
  have root : ContDiffOn ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade => completedRootFactor parameters grade pair.2.ofLp.1)
      (movingChartDomain parameters grade) :=
    (completedRootFactor_contDiffOn parameters grade).comp axes.contDiffOn
      (fun _ inside => inside.2)
  have seedPart := q23ContDiffOn_complexCLM_apply seedOperators root
  have tangent0 := ((coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 0)).restrictScalars ℝ).contDiff.comp
    ((tangentComponentMap parameters grade 0).contDiff.comp axes)
  have tangent1 := ((coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 1)).restrictScalars ℝ).contDiff.comp
    ((tangentComponentMap parameters grade 1).contDiff.comp axes)
  have tangent := ((fieldValueMap parameters grade tameTangentInclusion).restrictScalars ℝ).contDiff.comp
    (tangent0.add tangent1)
  have scalar : ContDiffOn ℝ ∞
      (fun pair : Seed.Parameters × XAmbient parameters grade => completedTameSeedScalarFamily parameters grade pair.1)
      (movingChartDomain parameters grade) :=
    (completedTameSeedScalarFamily_contDiffOn parameters grade).comp contDiff_fst.contDiffOn
      (fun _ inside => inside.1)
  exact ((seedPart.add tangent.contDiffOn).add fields.fst.contDiffOn).prodMk
    (scalar.add fields.snd.contDiffOn)

theorem completedChartFamily_agrees (parameters : PhaseParameters) (grade : ℕ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : XAmbient parameters grade) :
    completedChartFamily parameters grade (seed, state) = completedChart parameters seed inside grade state := by
  have fieldLaw : completedTameSeedFieldFamily parameters grade seed =
      fieldEmbed parameters 3 grade (tameSeedField parameters seed inside) :=
    completedTameSeedFieldFamily_core parameters grade seed inside
  have scalarLaw : completedTameSeedScalarFamily parameters grade seed =
      fieldEmbed parameters 1 grade (tameSeedScalar parameters seed inside) :=
    completedTameSeedScalarFamily_core parameters grade seed inside
  unfold completedChartFamily completedChart
  rw [fieldLaw, scalarLaw, completedCoefficientField_core]

end Grad.Q24Realization
