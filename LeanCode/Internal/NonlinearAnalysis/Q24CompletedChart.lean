import Q24AxisQuadratic
import Q24FieldLinear

noncomputable section

open scoped ContDiff

namespace Grad.Q24Realization

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearQuotientBounds Grad.AxisCore
open Grad.Q8FixedGrade Grad.SmoothingFamily Grad.Constraints Grad.ImplementationReadiness

def completedRootFactor (parameters : PhaseParameters) (grade : ℕ)
    (family : AxisGrade parameters 2 (grade + 1)) : Carrier parameters grade :=
  ∑' p, coefficientTerm p (completedTangentQuadratic parameters grade family)

theorem completedRootFactor_contDiffOn (parameters : PhaseParameters) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedRootFactor parameters grade) (axisDomain parameters grade) :=
  (root_series_contDiffOn parameters grade).1.comp
    (completedTangentQuadratic_contDiff parameters grade).contDiffOn
    (fun _ inside => axisDomain_quadratic_small parameters grade inside)

theorem completedRootFactor_core (parameters : PhaseParameters) (grade : ℕ)
    (family : TangentCoefficient parameters) (inside : tangentNorm 1 family < (2 * axisConstant)⁻¹) :
    completedRootFactor parameters grade (tangentToGrade parameters (grade + 1) family) =
      embed parameters grade (tameRootShifted 0 (tangentQuadratic family)) := by
  have small := axisDomain_quadratic_small parameters grade
    ((axisDomain_core_iff parameters grade family).2 inside)
  change lowNorm parameters grade
    (completedTangentQuadratic parameters grade (tangentToGrade parameters (grade + 1) family)) < 1 at small
  rw [completedTangentQuadratic_core, lowNorm_embed] at small
  rw [completedRootFactor, completedTangentQuadratic_core,
    rootSeries_completion_agrees parameters grade _ small, tameRootShifted_of_small 0 small]
  rfl

theorem stateAxis_contDiff (parameters : PhaseParameters) (grade : ℕ) :
    ContDiff ℝ ∞ (fun state : XAmbient parameters grade => state.ofLp.1) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ
    (AxisGrade parameters 2 (grade + 1))
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).contDiff.fst

theorem stateFields_contDiff (parameters : PhaseParameters) (grade : ℕ) :
    ContDiff ℝ ∞ (fun state : XAmbient parameters grade => state.ofLp.2.ofLp) :=
  (WithLp.prodContinuousLinearEquiv 1 ℝ (AGrade parameters 3 grade) (AGrade parameters 1 grade)).contDiff.comp
    (WithLp.prodContinuousLinearEquiv 1 ℝ (AxisGrade parameters 2 (grade + 1))
      (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).contDiff.snd

def chartDomain (parameters : PhaseParameters) (grade : ℕ) : Set (XAmbient parameters grade) :=
  {state | state.ofLp.1 ∈ axisDomain parameters grade}

theorem chartDomain_isOpen (parameters : PhaseParameters) (grade : ℕ) :
    IsOpen (chartDomain parameters grade) :=
  (axisDomain_isOpen parameters grade).preimage (stateAxis_contDiff parameters grade).continuous

/-- Literal Q18 on the completed original state carrier. The pair codomain
is only an intermediate chart target; the final quotient retains its Hilbert norm. -/
def completedChart (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (grade : ℕ) (state : XAmbient parameters grade) :
    AGrade parameters 3 grade × AGrade parameters 1 grade :=
  (coefficientFieldMap parameters 3 grade (tameSeedField parameters seed inside)
      (completedRootFactor parameters grade state.ofLp.1) +
    fieldValueMap parameters grade tameTangentInclusion
      (coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 0)
          (tangentComponentMap parameters grade 0 state.ofLp.1) +
        coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 1)
          (tangentComponentMap parameters grade 1 state.ofLp.1)) + state.ofLp.2.ofLp.1,
    fieldEmbed parameters 1 grade (tameSeedScalar parameters seed inside) + state.ofLp.2.ofLp.2)

theorem completedChart_contDiffOn (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (grade : ℕ) :
    ContDiffOn ℝ ∞ (completedChart parameters seed inside grade) (chartDomain parameters grade) := by
  have axisSmooth := stateAxis_contDiff parameters grade
  have fieldsSmooth := stateFields_contDiff parameters grade
  have rootSmooth := (completedRootFactor_contDiffOn parameters grade).comp axisSmooth.contDiffOn
    (fun _ membership => membership)
  have seedSmooth := ((coefficientFieldMap parameters 3 grade (tameSeedField parameters seed inside)).restrictScalars ℝ).contDiff.comp_contDiffOn rootSmooth
  have tangent0 := ((coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 0)).restrictScalars ℝ).contDiff.comp
    ((tangentComponentMap parameters grade 0).contDiff.comp axisSmooth)
  have tangent1 := ((coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 1)).restrictScalars ℝ).contDiff.comp
    ((tangentComponentMap parameters grade 1).contDiff.comp axisSmooth)
  have tangentSmooth := ((fieldValueMap parameters grade tameTangentInclusion).restrictScalars ℝ).contDiff.comp
    (tangent0.add tangent1)
  exact ((seedSmooth.add tangentSmooth.contDiffOn).add fieldsSmooth.fst.contDiffOn).prodMk
    ((contDiff_const.add fieldsSmooth.snd).contDiffOn)

def chartCoreEmbed (parameters : PhaseParameters) (grade : ℕ) (state : ChartState parameters) :
    XAmbient parameters grade :=
  statePack (tangentToGrade parameters (grade + 1) state.1)
    (fieldEmbed parameters 3 grade state.2.1) (fieldEmbed parameters 1 grade state.2.2)

theorem chartCoreEmbed_norm (parameters : PhaseParameters) (grade : ℕ) (state : ChartState parameters) :
    ‖chartCoreEmbed parameters grade state‖ = chartStateNorm grade state := by
  rw [chartCoreEmbed, statePack_norm, tangentToGrade_norm, fieldEmbed_norm, fieldEmbed_norm]
  rfl

theorem completedChart_core (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (grade : ℕ) (state : ChartState parameters)
    (axis : ChartAxisCondition state) :
    completedChart parameters seed inside grade (chartCoreEmbed parameters grade state) =
      (fieldEmbed parameters 3 grade (normalizedChart parameters seed inside state).1,
        fieldEmbed parameters 1 grade (normalizedChart parameters seed inside state).2) := by
  change (coefficientFieldMap parameters 3 grade (tameSeedField parameters seed inside)
    (completedRootFactor parameters grade (tangentToGrade parameters (grade + 1) state.1)) +
      fieldValueMap parameters grade tameTangentInclusion
        (coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 0)
            (tangentComponentMap parameters grade 0 (tangentToGrade parameters (grade + 1) state.1)) +
          coefficientFieldMap parameters 1 grade (tameCoordinateScalarField parameters 1)
            (tangentComponentMap parameters grade 1 (tangentToGrade parameters (grade + 1) state.1))) +
      fieldEmbed parameters 3 grade state.2.1,
      fieldEmbed parameters 1 grade (tameSeedScalar parameters seed inside) + fieldEmbed parameters 1 grade state.2.2) = _
  rw [completedRootFactor_core parameters grade state.1 axis]
  simp only [tangentComponentMap_core, coefficientFieldMap_core, ← map_add,
    fieldValueMap_core, normalizedChart]

end Grad.Q24Realization
