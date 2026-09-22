import CP14Consumer
import AX16ZConsumer

noncomputable section

open scoped BigOperators

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.GaugeCoefficients.Radial Grad.AxisCore

abbrev SmoothQuotient (parameters : PhaseParameters) := Fin 4 → ACore parameters 1

/-- The literal fourfold completion embedding, with no change of product norm. -/
def quotientEta (parameters : PhaseParameters) (grade : ℕ) :
    SmoothQuotient parameters →ₗ[ℂ] ZAmbient parameters grade :=
  (zEmbedding parameters grade).comp
    (LinearMap.pi fun coordinate =>
      (GradeCore.ofCoreLinear (parameters := parameters) (dimension := 1)
        (grade := grade)).comp (LinearMap.proj coordinate))

def quotientNorm (parameters : PhaseParameters) (grade : ℕ)
    (field : SmoothQuotient parameters) : ℝ := ‖quotientEta parameters grade field‖

/-- Reflection is only in the planar variable; no cell reversal or value conjugation. -/
def reflection (parameters : PhaseParameters) : ACore parameters 1 →ₗ[ℂ] ACore parameters 1 :=
  orthogonalCore parameters cartesianReflectionEquiv

theorem reflection_involutive (parameters : PhaseParameters) (field : ACore parameters 1) :
    reflection parameters (reflection parameters field) = field := by
  apply Subtype.ext
  funext cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (field.val cell).value
    (orthogonalClosedPoint cartesianReflectionEquiv
      (orthogonalClosedPoint cartesianReflectionEquiv point)) = _
  congr 1
  apply Subtype.ext
  exact cartesianReflection_involutive point.val

theorem reflection_angular (parameters : PhaseParameters) (mode : ℤ)
    (field : ACore parameters 1) :
    reflection parameters (angularCore parameters mode field) =
      angularCore parameters (-mode) (reflection parameters field) := by
  apply Subtype.ext
  funext cell
  exact angularClosedJet_reflection mode (field.val cell)

/-- N34's positive angular-mode coefficient. -/
def firstMode (parameters : PhaseParameters) :
    SmoothQuotient parameters →ₗ[ℂ] ACore parameters 1 :=
  (1 / 2 : ℂ) • ((angularCore parameters 1).comp (LinearMap.proj 0) +
    (reflection parameters).comp ((angularCore parameters (-1)).comp (LinearMap.proj 1)))

/-- The literal N34 projection K1, in the ordered spin coordinates. -/
def modeProjection (parameters : PhaseParameters) :
    SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi ![firstMode parameters, (reflection parameters).comp (firstMode parameters), 0, 0]

/-- N35, using the actual closed first-jet traces. -/
def affineTrace (parameters : PhaseParameters) :
    SmoothQuotient parameters →ₗ[ℂ] AxisSmoothCore parameters 1 :=
  (4 * Complex.I)⁻¹ •
    (((traceFirst 0 - Complex.I • traceFirst 1).comp (LinearMap.proj 0)) -
      ((traceFirst 0 + Complex.I • traceFirst 1).comp (LinearMap.proj 1)))

/-- N36 via z E0 = E1 + i E2 and bar(z) E0 = E1 - i E2. -/
def affineInsertion (parameters : PhaseParameters) :
    AxisSmoothCore parameters 1 →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi ![Complex.I • (insertOne 0 + Complex.I • insertOne 1),
    (-Complex.I) • (insertOne 0 - Complex.I • insertOne 1), 0, 0]

/-- Remove a mean on exactly one designated component. -/
def removeMean (parameters : PhaseParameters) (coordinate : Fin 4) :
    SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi fun index =>
    if index = coordinate then
      (LinearMap.id - angularCore parameters 0).comp (LinearMap.proj index)
    else LinearMap.proj index

/-- N38 in its exact written factor order, before any completion. -/
def quotientProjection (parameters : PhaseParameters) :
    SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  (LinearMap.id - (affineInsertion parameters).comp (affineTrace parameters)).comp
    ((LinearMap.id - modeProjection parameters).comp
      ((removeMean parameters 2).comp (removeMean parameters 3)))

theorem affineTrace_insertion (parameters : PhaseParameters)
    (family : AxisSmoothCore parameters 1) :
    affineTrace parameters (affineInsertion parameters family) = family := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (Complex.I • (insertOne 0 family + Complex.I • insertOne 1 family)) -
        Complex.I • traceFirst 1
          (Complex.I • (insertOne 0 family + Complex.I • insertOne 1 family))) -
      (traceFirst 0 ((-Complex.I) • (insertOne 0 family - Complex.I • insertOne 1 family)) +
        Complex.I • traceFirst 1
          ((-Complex.I) • (insertOne 0 family - Complex.I • insertOne 1 family)))) = family
  simp only [map_smul, map_add, map_sub, traceFirst_insertOne]
  norm_num
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  calc _ = -(Complex.I ^ 2) • family := by module
       _ = family := by simp

end Grad.QuotientProjection
