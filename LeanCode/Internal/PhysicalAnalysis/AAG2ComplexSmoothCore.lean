import AAG1ActualPhasePotential
import GQF2SourceCarriers

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.AnnularSourceGraph Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Complex scalar structure on exactly the accepted smooth radial graphs. -/
def complexSmoothRadialCore (dimension : ℕ) :
    Submodule ℂ (C(ℝ, ComplexEuclidean dimension) × C(ℝ, ComplexEuclidean dimension)) where
  carrier := {pair | ContDiff ℝ ∞ pair.1 ∧ ∀ radius, HasDerivAt pair.1 (pair.2 radius) radius}
  zero_mem' := ⟨contDiff_const, fun _ => hasDerivAt_const _ _⟩
  add_mem' := by
    intro first second firstLaw secondLaw
    exact ⟨firstLaw.1.add secondLaw.1, fun radius => (firstLaw.2 radius).add (secondLaw.2 radius)⟩
  smul_mem' := by
    intro scalar core law
    exact ⟨law.1.const_smul scalar, fun radius => (law.2 radius).const_smul scalar⟩

def complexCoreToAccepted (dimension : ℕ) :
    complexSmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension where
  toFun core := ⟨⟨core.val, core.property.2⟩, core.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def acceptedCoreToComplex (dimension : ℕ) :
    SmoothRadialCore dimension →ₗ[ℝ] complexSmoothRadialCore dimension where
  toFun core := ⟨core.val.val, core.property, core.val.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem complexCoreToAccepted_inverse (dimension : ℕ) (core : SmoothRadialCore dimension) :
    complexCoreToAccepted dimension (acceptedCoreToComplex dimension core) = core := rfl

theorem acceptedCoreToComplex_inverse (dimension : ℕ) (core : complexSmoothRadialCore dimension) :
    acceptedCoreToComplex dimension (complexCoreToAccepted dimension core) = core := rfl

def complexCoreValue (dimension : ℕ) :
    complexSmoothRadialCore dimension →ₗ[ℂ] C(ℝ, ComplexEuclidean dimension) :=
  (LinearMap.fst ℂ _ _).comp (complexSmoothRadialCore dimension).subtype

def complexCoreSlope (dimension : ℕ) :
    complexSmoothRadialCore dimension →ₗ[ℂ] C(ℝ, ComplexEuclidean dimension) :=
  (LinearMap.snd ℂ _ _).comp (complexSmoothRadialCore dimension).subtype

def complexCoreEndpoint (dimension : ℕ) (radius : ℝ) :
    complexSmoothRadialCore dimension →ₗ[ℂ] ComplexEuclidean dimension where
  toFun core := core.val.1 radius
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The existing literal square-root storage map, with its complex linearity. -/
def weightedCurveComplex (dimension : ℕ) (lower : ℝ) :
    C(ℝ, ComplexEuclidean dimension) →ₗ[ℂ] RadialL2 dimension lower where
  toFun := weightedCurveLinear dimension lower
  map_add' := (weightedCurveLinear dimension lower).map_add
  map_smul' scalar curve := by
    change radialToLp lower (scalar • curve) (scalar • curve).continuous =
      scalar • radialToLp lower curve curve.continuous
    apply Lp.ext
    filter_upwards [radialToLp_ae lower (scalar • curve) (scalar • curve).continuous,
      radialToLp_ae lower curve curve.continuous,
      Lp.coeFn_smul scalar (radialToLp lower curve curve.continuous)]
      with radius total curveLaw scaled
    rw [total, scaled, Pi.smul_apply, curveLaw]
    exact smul_comm (Real.sqrt radius) scalar (curve radius)

theorem weightedCurveComplex_eq (dimension : ℕ) (lower : ℝ)
    (curve : C(ℝ, ComplexEuclidean dimension)) :
    weightedCurveComplex dimension lower curve = weightedCurveLinear dimension lower curve := rfl

def continuousCurveWeight (dimension : ℕ) (coefficient : C(ℝ, ℝ)) :
    C(ℝ, ComplexEuclidean dimension) →ₗ[ℂ] C(ℝ, ComplexEuclidean dimension) where
  toFun curve := ⟨fun radius => coefficient radius • curve radius,
    coefficient.continuous.smul curve.continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro radius
    exact smul_add (coefficient radius) (first radius) (second radius)
  map_smul' scalar curve := by
    apply ContinuousMap.ext
    intro radius
    exact smul_comm (coefficient radius) scalar (curve radius)

end Grad.AnnularVariational
