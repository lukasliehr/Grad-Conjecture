import GC20H1Trace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.GenericCarriers

local instance physicalRealInner (dimension : ℕ) : InnerProductSpace ℝ (PhysicalValue dimension) :=
  InnerProductSpace.rclikeToReal ℂ (PhysicalValue dimension)

structure CollarTest (lower : ℝ) where
  value : C(ℝ, ℝ)
  derivative : C(ℝ, ℝ)
  derivativeLaw : ∀ radius, HasDerivAt value (derivative radius) radius
  lowerZero : value lower = 0
  upperZero : value 1 = 0

def collarTestCurve {dimension : ℕ} (test : C(ℝ, ℝ)) (vector : PhysicalValue dimension) : C(ℝ, PhysicalValue dimension) :=
  ⟨fun radius => test radius • vector, test.continuous.smul continuous_const⟩

def collarPairing {dimension : ℕ} (lower : ℝ) (test : C(ℝ, ℝ)) (vector : PhysicalValue dimension) :
    CollarL2 (PhysicalValue dimension) lower →L[ℝ] ℂ :=
  (innerSL ℂ (collarContinuousL2 (PhysicalValue dimension) lower (collarTestCurve test vector))).restrictScalars ℝ

theorem collarPairing_integral {dimension : ℕ} (lower : ℝ) (test : C(ℝ, ℝ)) (vector : PhysicalValue dimension)
    (field : CollarL2 (PhysicalValue dimension) lower) :
    collarPairing lower test vector field = ∫ radius in Icc lower 1, test radius • inner ℂ vector (field radius) := by
  change inner ℂ (collarContinuousL2 (PhysicalValue dimension) lower (collarTestCurve test vector)) field = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(collarContinuous_memLp (PhysicalValue dimension) lower (collarTestCurve test vector)).coeFn_toLp]
    with radius representative
  change collarContinuousL2 (PhysicalValue dimension) lower (collarTestCurve test vector) radius = _ at representative
  rw [representative]
  exact inner_smul_left_eq_smul _ _ _

theorem collarPairing_core {dimension : ℕ} (lower : ℝ) (bounded : lower ≤ 1)
    (test : C(ℝ, ℝ)) (vector : PhysicalValue dimension) (field : C(ℝ, PhysicalValue dimension)) :
    collarPairing lower test vector (collarContinuousL2 (PhysicalValue dimension) lower field) =
      ∫ radius in lower..1, test radius • inner ℂ vector (field radius) := by
  rw [collarPairing_integral, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [(collarContinuous_memLp (PhysicalValue dimension) lower field).coeFn_toLp] with radius representative
  change collarContinuousL2 (PhysicalValue dimension) lower field radius = _ at representative
  rw [representative]

def CollarWeakDerivative {dimension : ℕ} (lower : ℝ)
    (field derivative : CollarL2 (PhysicalValue dimension) lower) : Prop :=
  ∀ (test : CollarTest lower) (vector : PhysicalValue dimension),
    collarPairing lower test.value vector derivative = -collarPairing lower test.derivative vector field

theorem collarCore_weak {dimension : ℕ} (lower : ℝ) (bounded : lower ≤ 1)
    (core : collarSmoothGraph (PhysicalValue dimension)) :
    CollarWeakDerivative lower (collarContinuousL2 (PhysicalValue dimension) lower core.val.1)
      (collarContinuousL2 (PhysicalValue dimension) lower core.val.2) := by
  intro test vector
  rw [collarPairing_core lower bounded, collarPairing_core lower bounded]
  let pairing := (innerSL ℂ vector).restrictScalars ℝ
  have pairedDerivative (radius : ℝ) :
      HasDerivAt (fun point => inner ℂ vector (core.val.1 point)) (inner ℂ vector (core.val.2 radius)) radius :=
    pairing.hasFDerivAt.comp_hasDerivAt radius (core.property radius)
  have identity := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := lower) (b := 1) (fun radius _ => test.derivativeLaw radius)
    (fun radius _ => pairedDerivative radius)
    (test.derivative.continuous.intervalIntegrable lower 1)
    ((pairing.continuous.comp core.val.2.continuous).intervalIntegrable lower 1)
  simpa only [test.lowerZero, test.upperZero, zero_smul, sub_self, zero_sub] using identity

theorem collarH1_weak {dimension : ℕ} (lower : ℝ) (bounded : lower ≤ 1)
    (field : CollarH1 (PhysicalValue dimension) lower) :
    CollarWeakDerivative lower (collarH1Coordinate (PhysicalValue dimension) lower 0 field)
      (collarH1Coordinate (PhysicalValue dimension) lower 1 field) := by
  intro test vector
  apply isClosed_property (collarH1Core_denseRange (PhysicalValue dimension) lower)
    (isClosed_eq
      ((collarPairing lower test.value vector).continuous.comp (collarH1Coordinate (PhysicalValue dimension) lower 1).continuous)
      (((collarPairing lower test.derivative vector).continuous.comp
        (collarH1Coordinate (PhysicalValue dimension) lower 0).continuous).neg)) _ field
  intro core
  exact collarCore_weak lower bounded core test vector

def collarCompactTest (lower : ℝ) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioo lower 1) : CollarTest lower where
  value := ⟨test, smooth.continuous⟩
  derivative := ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
  derivativeLaw := fun radius => (smooth.differentiable (by simp) radius).hasDerivAt
  lowerZero := by
    by_contra member
    have := supported (subset_closure member)
    exact (lt_irrefl lower) this.1
  upperZero := by
    by_contra member
    have := supported (subset_closure member)
    exact (lt_irrefl (1 : ℝ)) this.2

theorem collarPairing_separates {dimension : ℕ} (lower : ℝ)
    (field : CollarL2 (PhysicalValue dimension) lower)
    (vanishes : ∀ (test : CollarTest lower) (vector : PhysicalValue dimension), collarPairing lower test.value vector field = 0) :
    field = 0 := by
  have coordinateZero (coordinate : Fin dimension) :
      ∀ᵐ radius ∂volume.restrict (Icc lower 1), field radius coordinate = 0 := by
    let vector : PhysicalValue dimension := EuclideanSpace.single coordinate (1 : ℂ)
    let scalar : ℝ → ℂ := fun radius => inner ℂ vector (field radius)
    have locallyIntegrable : LocallyIntegrable scalar (volume.restrict (Icc lower 1)) :=
      ((innerSL ℂ vector).comp_memLp field).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
    have zeroOn : ∀ᵐ radius ∂volume.restrict (Icc lower 1), radius ∈ Ioo lower 1 → scalar radius = 0 := by
      apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (locallyIntegrable.locallyIntegrableOn (Ioo lower 1))
      intro test smooth _compact supported
      change (∫ radius in Icc lower 1, (⟨test, smooth.continuous⟩ : C(ℝ, ℝ)) radius • inner ℂ vector (field radius)) = 0
      rw [← collarPairing_integral lower ⟨test, smooth.continuous⟩ vector field]
      exact vanishes (collarCompactTest lower test smooth supported) vector
    have inside : ∀ᵐ radius ∂volume.restrict (Icc lower 1), radius ∈ Ioo lower 1 := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [zeroOn, inside] with radius zeroAt insideAt
    simpa only [scalar, vector, EuclideanSpace.inner_single_left, map_one, one_mul] using zeroAt insideAt
  apply Lp.ext
  filter_upwards [ae_all_iff.2 coordinateZero, Lp.coeFn_zero (PhysicalValue dimension) 2 (volume.restrict (Icc lower 1))]
    with radius coordinates zeroRepresentative
  rw [zeroRepresentative]
  apply PiLp.ext
  intro coordinate
  exact coordinates coordinate

theorem collarH1_value_injective {dimension : ℕ} (lower : ℝ) (bounded : lower ≤ 1) :
    Function.Injective (collarH1Coordinate (PhysicalValue dimension) lower 0) := by
  intro first second sameValue
  have sameDerivative : collarH1Coordinate (PhysicalValue dimension) lower 1 first =
      collarH1Coordinate (PhysicalValue dimension) lower 1 second := by
    apply sub_eq_zero.mp
    apply collarPairing_separates lower
    intro test vector
    rw [map_sub, collarH1_weak lower bounded first test vector, collarH1_weak lower bounded second test vector,
      sameValue, sub_self]
  apply Subtype.ext
  apply PiLp.ext
  intro entry
  fin_cases entry
  · exact sameValue
  · exact sameDerivative

end Grad.GaugeCoefficients.Physical.WeightedTrace
