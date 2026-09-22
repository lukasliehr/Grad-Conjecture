import AXF24CartesianTraces

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.AxisSplit Grad.AxisJet Grad.AxisCore

variable {parameters : PhaseParameters}

/-- Literal Jy E0: the components are -E_2 and E_1, as in BS6. -/
def curlInsertion : AxisSmoothCore parameters 1 →ₗ[ℂ] ACore parameters 2 :=
  -(Grad.Constraints.valueMapCore (componentInsertion 0) parameters).comp (radialFirstInsertion 1) +
    (Grad.Constraints.valueMapCore (componentInsertion 1) parameters).comp (radialFirstInsertion 0)

theorem curlInsertion_tuple (data : AxisSmoothCore parameters 1) :
    curlInsertion data = vectorTuple (-radialFirstInsertion 1 data) (radialFirstInsertion 0 data) := by
  change -Grad.Constraints.valueMapCore (componentInsertion 0) parameters (radialFirstInsertion 1 data) +
    Grad.Constraints.valueMapCore (componentInsertion 1) parameters (radialFirstInsertion 0 data) = _
  rw [vectorTuple, map_neg]

theorem cartesianSourceVector_radialAffineInsertion (data : AxisSmoothCore parameters 1) :
    cartesianSourceVector (radialAffineInsertion data) = curlInsertion data := by
  apply spinCore_joint_injective
  · rw [spinCore_cartesianSource_plus, curlInsertion_tuple, spinCore_components,
      componentCore_vectorTuple, componentCore_vectorTuple]
    change Complex.I • (radialFirstInsertion 0 data + Complex.I • radialFirstInsertion 1 data) =
      -radialFirstInsertion 1 data + (1 * Complex.I) • radialFirstInsertion 0 data
    simp only [smul_add, smul_smul, Complex.I_mul_I, neg_one_smul, one_mul]
    module
  · rw [spinCore_cartesianSource_minus, curlInsertion_tuple, spinCore_components,
      componentCore_vectorTuple, componentCore_vectorTuple]
    change (-Complex.I) • (radialFirstInsertion 0 data - Complex.I • radialFirstInsertion 1 data) =
      -radialFirstInsertion 1 data + (-1 * Complex.I) • radialFirstInsertion 0 data
    calc _ = (-Complex.I) • radialFirstInsertion 0 data +
        Complex.I ^ 2 • radialFirstInsertion 1 data := by module
         _ = _ := by rw [Complex.I_sq]; module

theorem cartesianSourceVector_meanPair (source : SmoothQuotient parameters) :
    cartesianSourceVector (meanPair parameters source) = cartesianSourceVector source := rfl

theorem cartesianSourceVector_fourthCorrection (source : SmoothQuotient parameters) :
    cartesianSourceVector (fourthCorrection source) = 0 := by
  apply spinCore_joint_injective
  · rw [spinCore_cartesianSource_plus, map_zero]
    rfl
  · rw [spinCore_cartesianSource_minus, map_zero]
    rfl

def cartesianValueReduced (source : SmoothQuotient parameters) : ACore parameters 2 :=
  let v := cartesianSourceVector source - radialSourceCore parameters (cartesianSourceVector source)
  v - fixedValueCorrection v

theorem cartesianValueReduced_eq (source : SmoothQuotient parameters) :
    cartesianSourceVector (source - modeProjection parameters source -
      valueCorrection (source - modeProjection parameters source)) = cartesianValueReduced source := by
  change cartesianSourceLinear (source - modeProjection parameters source -
    valueCorrection (source - modeProjection parameters source)) = _
  rw [map_sub, map_sub]
  simp only [cartesianSourceLinear_apply]
  rw [cartesianSourceVector_valueCorrection]
  change _ = (cartesianSourceVector source - radialSourceCore parameters (cartesianSourceVector source)) -
    fixedValueCorrection (cartesianSourceVector source - radialSourceCore parameters (cartesianSourceVector source))
  rw [cartesianSourceVector_modeProjection]
  congr 1
  change fixedValueCorrection (cartesianSourceLinear (source - modeProjection parameters source)) = _
  rw [map_sub]
  simp only [cartesianSourceLinear_apply, cartesianSourceVector_modeProjection]

theorem affineTrace_valueReduced (source : SmoothQuotient parameters) :
    affineTrace parameters source =
      (1 / 2 : ℂ) • cartesianCurlTrace (cartesianValueReduced source) := by
  rw [← cartesianValueReduced_eq, ← affineTrace_cartesian_curl,
    map_sub, map_sub, affineTrace_modeProjection, affineTrace_valueCorrection,
    sub_zero, sub_zero]

/-- Exact BS6 vector formula, including the order of the value and curl
corrections and the fixed radial profile. -/
theorem cartesianSourceVector_flatSourceProjection (source : SmoothQuotient parameters) :
    cartesianSourceVector (flatSourceProjection source) =
      cartesianValueReduced source - (1 / 2 : ℂ) •
        curlInsertion (cartesianCurlTrace (cartesianValueReduced source)) := by
  rw [flatSourceProjection_apply]
  change cartesianSourceLinear (meanPair parameters source - modeProjection parameters source -
    valueCorrection (source - modeProjection parameters source) -
    radialAffineInsertion (affineTrace parameters source) - fourthCorrection source) = _
  rw [map_sub, map_sub, map_sub, map_sub]
  simp only [cartesianSourceLinear_apply]
  rw [cartesianSourceVector_meanPair, cartesianSourceVector_fourthCorrection, sub_zero,
    cartesianSourceVector_radialAffineInsertion, affineTrace_valueReduced, map_smul]
  congr 1
  rw [← cartesianValueReduced_eq]
  change _ = cartesianSourceLinear (source - modeProjection parameters source -
    valueCorrection (source - modeProjection parameters source))
  simp only [map_sub, cartesianSourceLinear_apply]
  congr 1
  exact cartesianSourceLinear.map_sub _ _

end Grad.FlatSourceProjection
