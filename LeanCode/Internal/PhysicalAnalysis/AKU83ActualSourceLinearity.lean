import AKU82ActualJCSourcePayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Ledger

abbrev FiniteAxisData (parameters : PhaseParameters) (dimension : ℕ) := Grad.AxisCore.AxisSmoothCore parameters dimension

def finiteQuadraticOperatorLinear (parameters : PhaseParameters) :
    (Fin 3 → FiniteAxisData parameters 2) →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 2) :=
  LinearMap.pi (fun index => ![LinearMap.proj 1,(2 : ℂ) • LinearMap.proj 2-(2 : ℂ) • LinearMap.proj 0,-LinearMap.proj 1] index +
    (axisValueMap (parameters := parameters) quarterValueMap).comp (LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) index))

def finiteQuadraticInverseLinear (parameters : PhaseParameters) :
    (Fin 3 → FiniteAxisData parameters 2) →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 2) :=
  -(1/9 : ℂ) • ((finiteQuadraticOperatorLinear parameters).comp
    ((finiteQuadraticOperatorLinear parameters).comp (finiteQuadraticOperatorLinear parameters))+
      (10 : ℂ) • finiteQuadraticOperatorLinear parameters)

def finiteForce2Linear (parameters : PhaseParameters) : SmoothQuotient parameters →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 2) :=
  LinearMap.pi (fun index => ![(1/2 : ℂ) • (traceFirst 0).comp ((partialCore parameters 0).comp cartesianSourceLinear),
    (traceFirst 0).comp ((partialCore parameters 1).comp cartesianSourceLinear),
    (1/2 : ℂ) • (traceFirst 1).comp ((partialCore parameters 1).comp cartesianSourceLinear)] index)

def finiteHessianLinear (parameters : PhaseParameters) : SmoothQuotient parameters →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 1) :=
  LinearMap.pi (fun index => ![(1/2 : ℂ) • (traceFirst 0).comp cartesianSpinFirst,
    (traceFirst 1).comp cartesianSpinFirst,(1/2 : ℂ) • (traceFirst 1).comp cartesianSpinSecond] index)

def finiteScalarSecondLinear (parameters : PhaseParameters) : ACore parameters 1 →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 1) :=
  LinearMap.pi (fun index => ![(1/2 : ℂ) • (traceFirst 0).comp (partialCore parameters 0),
    (traceFirst 0).comp (partialCore parameters 1),(1/2 : ℂ) • (traceFirst 1).comp (partialCore parameters 1)] index)

def finiteTimeSourceLinear (parameters : PhaseParameters) : SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi (fun row => (timeDerivativeCore parameters).comp (LinearMap.proj row))

def finiteToroidalTargetLinear (parameters : PhaseParameters) : SmoothQuotient parameters →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 1) :=
  (finiteScalarSecondLinear parameters).comp (LinearMap.proj 3)+
    (finiteHessianLinear parameters).comp (finiteTimeSourceLinear parameters)

def finiteC2Linear (parameters : PhaseParameters) (length : ℝ) : SmoothQuotient parameters →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 1) :=
  (length : ℂ)⁻¹ • LinearMap.pi (fun index => ![-(1/4 : ℂ) • (LinearMap.proj 1).comp (finiteToroidalTargetLinear parameters),
    (LinearMap.proj 0).comp (finiteToroidalTargetLinear parameters),
    (1/4 : ℂ) • (LinearMap.proj 1).comp (finiteToroidalTargetLinear parameters)] index)

def finiteCovectorLinear (parameters : PhaseParameters) :
    (FiniteAxisData parameters 2 × FiniteAxisData parameters 1) →ₗ[ℂ] FiniteAxisData parameters 3 :=
  (axisValueMap (matrixOperator firstTwoInclusion)).comp (LinearMap.fst ℂ _ _)+
    (axisValueMap (matrixOperator (!![0;0;1] : Matrix (Fin 3) (Fin 1) ℂ))).comp (LinearMap.snd ℂ _ _)

def finiteDivergenceLinear (parameters : PhaseParameters) :
    (Fin 3 → FiniteAxisData parameters 2) →ₗ[ℂ] FiniteAxisData parameters 2 :=
  (axisValueMap scalarAxisPairFirst).comp
    ((2 : ℂ) • (axisComponent (parameters := parameters) (dimension := 2) 0).comp (LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 0)+(axisComponent (parameters := parameters) (dimension := 2) 1).comp (LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 1))+
  (axisValueMap scalarAxisPairSecond).comp
    ((axisComponent (parameters := parameters) (dimension := 2) 0).comp (LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 1)+(2 : ℂ) • (axisComponent (parameters := parameters) (dimension := 2) 1).comp (LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 2))

def finiteComplementLinear (parameters : PhaseParameters) :
    FiniteAxisData parameters 2 →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 2) :=
  LinearMap.pi (fun index => ![
    (axisValueMap scalarAxisPairFirst).comp ((5/3 : ℂ) • axisComponent (parameters := parameters) (dimension := 2) 1)+
      (axisValueMap scalarAxisPairSecond).comp (-(7/3 : ℂ) • axisComponent (parameters := parameters) (dimension := 2) 0),
    (axisValueMap scalarAxisPairFirst).comp ((2/3 : ℂ) • axisComponent (parameters := parameters) (dimension := 2) 0)+
      (axisValueMap scalarAxisPairSecond).comp (-(2/3 : ℂ) • axisComponent (parameters := parameters) (dimension := 2) 1),
    (axisValueMap scalarAxisPairFirst).comp ((7/3 : ℂ) • axisComponent (parameters := parameters) (dimension := 2) 1)+
      (axisValueMap scalarAxisPairSecond).comp (-(5/3 : ℂ) • axisComponent (parameters := parameters) (dimension := 2) 0)] index)

theorem finiteQuadraticOperatorLinear_apply (parameters : PhaseParameters) (data : Fin 3 → FiniteAxisData parameters 2) :
    finiteQuadraticOperatorLinear parameters data = quadraticAxisPlanarOperator data := by
  funext index
  fin_cases index <;> rfl

theorem finiteQuadraticInverseLinear_apply (parameters : PhaseParameters) (data : Fin 3 → FiniteAxisData parameters 2) :
    finiteQuadraticInverseLinear parameters data = quadraticAxisPlanarInverse data := by
  simp only [finiteQuadraticInverseLinear,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,
    finiteQuadraticOperatorLinear_apply]
  rfl

theorem finiteForce2Linear_apply (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    finiteForce2Linear parameters source = originalForce2Axis source := by
  funext index
  fin_cases index <;> rfl

theorem finiteHessianLinear_apply (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    finiteHessianLinear parameters source = originalScalarHessianAxis source := by
  funext index
  fin_cases index <;> rfl

theorem finiteC2Linear_apply (parameters : PhaseParameters) (length : ℝ) (source : SmoothQuotient parameters) :
    finiteC2Linear parameters length source = originalC2Axis length source := by
  funext index
  fin_cases index <;> rfl

theorem finiteCovectorLinear_apply (parameters : PhaseParameters) (data : FiniteAxisData parameters 2 × FiniteAxisData parameters 1) :
    finiteCovectorLinear parameters data = axisCovectorTriple data.1 data.2 := rfl

theorem finiteDivergenceLinear_apply (parameters : PhaseParameters) (data : Fin 3 → FiniteAxisData parameters 2) :
    finiteDivergenceLinear parameters data = axisQuadraticDivergence data := rfl

theorem finiteComplementLinear_apply (parameters : PhaseParameters) (data : FiniteAxisData parameters 2) :
    finiteComplementLinear parameters data = axisCubicComplementVector data := by
  funext index
  fin_cases index <;> rfl

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
  (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)

def finiteCubicTargetLinear : SmoothQuotient parameters →ₗ[ℂ] FiniteAxisData parameters 2 :=
  let oldLow := (originalCubic_low_margin parameters length rho epsilon field low).1
  let determinantAction := axisFamilyAction (originalAxisInverseDeterminantFamily parameters length epsilon field)
    (originalAxisInverseDeterminantFamily_estimate parameters length rho epsilon field oldLow).actualCoherent
  let metricAction := axisFamilyAction (originalAxisMetricRowsFamily parameters length epsilon field)
    (originalAxisMetricRowsFamily_estimate parameters length rho epsilon field oldLow).actualCoherent
  let force := (finiteQuadraticInverseLinear parameters).comp (finiteForce2Linear parameters)
  let metricRows := LinearMap.pi (fun index : Fin 3 => metricAction.comp ((finiteCovectorLinear parameters).comp
    ((-((LinearMap.proj index).comp force)).prod ((LinearMap.proj index).comp (finiteC2Linear parameters length)))))
  (length : ℂ)⁻¹ • ((axisValueMap scalarAxisPairFirst).comp (determinantAction.comp ((traceFirst 0).comp (LinearMap.proj 2)))+
    (axisValueMap scalarAxisPairSecond).comp (determinantAction.comp ((traceFirst 1).comp (LinearMap.proj 2))))-
      (finiteDivergenceLinear parameters).comp metricRows

def finiteEllLinear : SmoothQuotient parameters →ₗ[ℂ] FiniteAxisData parameters 2 :=
  (axisFamilyAction (originalCubicInverseFamily parameters length epsilon field)
    (originalCubicInverseFamily_coherent parameters length rho epsilon field low)).comp
      (finiteCubicTargetLinear parameters length rho epsilon field low)

def finitePlanarLinear : SmoothQuotient parameters →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 2) :=
  (finiteComplementLinear parameters).comp (finiteEllLinear parameters length rho epsilon field low)-
    (finiteQuadraticInverseLinear parameters).comp (finiteForce2Linear parameters)

def finiteUAxisLinear : SmoothQuotient parameters →ₗ[ℂ] (Fin 3 → FiniteAxisData parameters 3) :=
  LinearMap.pi (fun index => (axisFamilyAction (originalAxisInverseTransposeFamily parameters length epsilon field)
    (originalAxisInverseTransposeFamily_estimate parameters length rho epsilon field
      (originalCubic_low_margin parameters length rho epsilon field low).1).actualCoherent).comp
    ((finiteCovectorLinear parameters).comp
      (((LinearMap.proj index).comp (finitePlanarLinear parameters length rho epsilon field low)).prod
        ((LinearMap.proj index).comp (finiteC2Linear parameters length)))))

def finiteS3AxisLinear : SmoothQuotient parameters →ₗ[ℂ] (Fin 4 → FiniteAxisData parameters 1) :=
  let linear := finiteEllLinear parameters length rho epsilon field low
  let planar := finitePlanarLinear parameters length rho epsilon field low
  LinearMap.pi (fun index => ![(axisComponent (parameters := parameters) (dimension := 2) 0).comp linear+(axisComponent (parameters := parameters) (dimension := 2) 1).comp ((LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 0).comp planar),
    (axisComponent (parameters := parameters) (dimension := 2) 1).comp linear+(axisComponent (parameters := parameters) (dimension := 2) 1).comp ((LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 1).comp planar)-(axisComponent (parameters := parameters) (dimension := 2) 0).comp ((LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 0).comp planar),
    (axisComponent (parameters := parameters) (dimension := 2) 0).comp linear+(axisComponent (parameters := parameters) (dimension := 2) 1).comp ((LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 2).comp planar)-(axisComponent (parameters := parameters) (dimension := 2) 0).comp ((LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 1).comp planar),
    (axisComponent (parameters := parameters) (dimension := 2) 1).comp linear-(axisComponent (parameters := parameters) (dimension := 2) 0).comp ((LinearMap.proj (φ := fun _ : Fin 3 => FiniteAxisData parameters 2) 2).comp planar)] index)

def originalFiniteLiftULinear : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 3 :=
  ∑ index : Fin 3, (vectorAxisProfileCore ((localizedFiniteJetLinear 3).comp (quadraticVectorMonomial 3 index))).comp
    ((LinearMap.proj index).comp (finiteUAxisLinear parameters length rho epsilon field low))

def originalFiniteLiftSLinear : SmoothQuotient parameters →ₗ[ℂ] ACore parameters 1 :=
  (∑ index : Fin 3, (fixedAxisJetCore (localizedFiniteJet (quadraticScalarJet (Pi.single index 1)))).comp
    ((LinearMap.proj index).comp (finiteHessianLinear parameters)))+
  ∑ index : Fin 4, (fixedAxisJetCore (localizedFiniteJet (cubicScalarJet (Pi.single index 1)))).comp
    ((LinearMap.proj index).comp (finiteS3AxisLinear parameters length rho epsilon field low))

theorem finiteCubicTargetLinear_apply (source : SmoothQuotient parameters) :
    finiteCubicTargetLinear parameters length rho epsilon field low source =
      originalCubicTargetAxis parameters length rho epsilon field low source := by
  dsimp only [finiteCubicTargetLinear,originalCubicTargetAxis,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.add_apply,LinearMap.proj_apply]
  apply congrArg₂ (· - ·)
  · rfl
  · rw [finiteDivergenceLinear_apply]
    apply congrArg axisQuadraticDivergence
    funext index
    simp only [LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.prod_apply,Function.prod,LinearMap.proj_apply,
      LinearMap.neg_apply,finiteCovectorLinear_apply,finiteC2Linear_apply,
      finiteQuadraticInverseLinear_apply,finiteForce2Linear_apply]


theorem finiteEllLinear_apply (source : SmoothQuotient parameters) :
    finiteEllLinear parameters length rho epsilon field low source =
      originalLiftEllAxis parameters length rho epsilon field low source := by
  simp only [finiteEllLinear,LinearMap.comp_apply,finiteCubicTargetLinear_apply]
  rfl

theorem finitePlanarLinear_apply (source : SmoothQuotient parameters) :
    finitePlanarLinear parameters length rho epsilon field low source =
      originalLiftPlanarAxis parameters length rho epsilon field low source := by
  simp only [finitePlanarLinear,LinearMap.sub_apply,LinearMap.comp_apply,finiteEllLinear_apply,
    finiteComplementLinear_apply,finiteForce2Linear_apply,finiteQuadraticInverseLinear_apply]
  rfl

theorem finiteUAxisLinear_apply (source : SmoothQuotient parameters) :
    finiteUAxisLinear parameters length rho epsilon field low source =
      originalLiftPhysicalUAxis parameters length rho epsilon field low source := by
  funext index
  simp only [finiteUAxisLinear,LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.prod_apply,Function.prod,LinearMap.proj_apply,
    finitePlanarLinear_apply,finiteC2Linear_apply,finiteCovectorLinear_apply]
  rfl

theorem finiteS3AxisLinear_apply (source : SmoothQuotient parameters) :
    finiteS3AxisLinear parameters length rho epsilon field low source =
      originalLiftS3Axis parameters length rho epsilon field low source := by
  funext index
  fin_cases index
  · change axisComponent 0 (finiteEllLinear parameters length rho epsilon field low source)+
      axisComponent 1 (finitePlanarLinear parameters length rho epsilon field low source 0) = _
    rw [finiteEllLinear_apply,finitePlanarLinear_apply]
    rfl
  · change axisComponent 1 (finiteEllLinear parameters length rho epsilon field low source)+
      axisComponent 1 (finitePlanarLinear parameters length rho epsilon field low source 1)-
      axisComponent 0 (finitePlanarLinear parameters length rho epsilon field low source 0) = _
    rw [finiteEllLinear_apply,finitePlanarLinear_apply]
    rfl
  · change axisComponent 0 (finiteEllLinear parameters length rho epsilon field low source)+
      axisComponent 1 (finitePlanarLinear parameters length rho epsilon field low source 2)-
      axisComponent 0 (finitePlanarLinear parameters length rho epsilon field low source 1) = _
    rw [finiteEllLinear_apply,finitePlanarLinear_apply]
    rfl
  · change axisComponent 1 (finiteEllLinear parameters length rho epsilon field low source)-
      axisComponent 0 (finitePlanarLinear parameters length rho epsilon field low source 2) = _
    rw [finiteEllLinear_apply,finitePlanarLinear_apply]
    rfl


theorem originalFiniteLiftULinear_apply (source : SmoothQuotient parameters) :
    originalFiniteLiftULinear parameters length rho epsilon field low source =
      originalFiniteLiftU parameters length rho epsilon field low source := by
  simp only [originalFiniteLiftULinear,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply]
  rw [finiteUAxisLinear_apply]
  rfl

theorem originalFiniteLiftSLinear_apply (source : SmoothQuotient parameters) :
    originalFiniteLiftSLinear parameters length rho epsilon field low source =
      originalFiniteLiftS parameters length rho epsilon field low source := by
  simp only [originalFiniteLiftSLinear,LinearMap.add_apply,LinearMap.sum_apply,LinearMap.comp_apply,LinearMap.proj_apply,finiteHessianLinear_apply,finiteS3AxisLinear_apply]
  rfl

def originalRealFiniteLiftULinear : SmoothQuotient parameters →ₗ[ℝ] ACore parameters 3 :=
  finiteRealCore.comp ((originalFiniteLiftULinear parameters length rho epsilon field low).restrictScalars ℝ)

def originalRealFiniteLiftSLinear : SmoothQuotient parameters →ₗ[ℝ] ACore parameters 1 :=
  finiteRealCore.comp ((originalFiniteLiftSLinear parameters length rho epsilon field low).restrictScalars ℝ)

end Grad.FinitePhysicalJetLift
