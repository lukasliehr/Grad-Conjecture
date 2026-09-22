import AKI20FaithfulOriginalSourceGraphCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Interval
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

local instance originalRealInner (dimension : ℕ) : InnerProductSpace ℝ (ComplexEuclidean dimension) :=
  InnerProductSpace.rclikeToReal ℂ (ComplexEuclidean dimension)

/-- Closed-collar classical derivatives imply the genuine weak graph law.
Only one-sided endpoint derivatives are required. -/
theorem collarWeakDerivative_of_closedClassical {dimension : ℕ} (lower : ℝ) (bounded : lower ≤ 1)
    (value slope : C(ℝ, ComplexEuclidean dimension))
    (derivative : ∀ radius ∈ Icc lower 1, HasDerivWithinAt value (slope radius) (Icc lower 1) radius) :
    CollarWeakDerivative lower (collarContinuousL2 (ComplexEuclidean dimension) lower value)
      (collarContinuousL2 (ComplexEuclidean dimension) lower slope) := by
  intro test vector
  rw [collarPairing_core (dimension := dimension) lower bounded test.value vector slope,
    collarPairing_core (dimension := dimension) lower bounded test.derivative vector value]
  let pairing := (innerSL ℂ vector).restrictScalars ℝ
  have paired (radius : ℝ) (inside : radius ∈ Icc lower 1) :
      HasDerivWithinAt (fun point => inner ℂ vector (value point)) (inner ℂ vector (slope radius)) (Icc lower 1) radius :=
    pairing.hasFDerivAt.comp_hasDerivWithinAt radius (derivative radius inside)
  have identity := intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (a := lower) (b := 1) (v := fun radius => inner ℂ vector (value radius))
    (v' := fun radius => inner ℂ vector (slope radius))
    (fun radius _ => (test.derivativeLaw radius).hasDerivWithinAt)
    (fun radius inside => by simpa only [uIcc_of_le bounded] using paired radius (by simpa only [uIcc_of_le bounded] using inside))
    (test.derivative.continuous.intervalIntegrable lower 1)
    ((pairing.continuous.comp slope.continuous).intervalIntegrable lower 1)
  simpa only [test.lowerZero, test.upperZero, zero_smul, sub_self, zero_sub] using identity

/-- The derivative coordinate in the actual weak graph is unique. -/
theorem collarWeakDerivative_unique {dimension : ℕ} (lower : ℝ)
    {value first second : CollarL2 (ComplexEuclidean dimension) lower}
    (firstWeak : CollarWeakDerivative lower value first)
    (secondWeak : CollarWeakDerivative lower value second) : first = second := by
  apply sub_eq_zero.mp
  apply collarPairing_separates lower
  intro test vector
  rw [map_sub, firstWeak test vector, secondWeak test vector, sub_self]

/-- A closed-classical representative and its actual L2 slope determine the
stored weak derivative; no slope equation is assumed for the candidate. -/
theorem collarWeakDerivative_of_representatives {dimension : ℕ} (lower : ℝ) (bounded : lower ≤ 1)
    (value slope : CollarL2 (ComplexEuclidean dimension) lower)
    (curve rhs : C(ℝ, ComplexEuclidean dimension))
    (valueSame : value =ᵐ[volume.restrict (Icc lower 1)] curve)
    (slopeSame : slope =ᵐ[volume.restrict (Icc lower 1)] rhs)
    (derivative : ∀ radius ∈ Icc lower 1, HasDerivWithinAt curve (rhs radius) (Icc lower 1) radius) :
    CollarWeakDerivative lower value slope := by
  have first : value = collarContinuousL2 (ComplexEuclidean dimension) lower curve := by
    apply Lp.ext
    exact valueSame.trans (collarContinuous_memLp (ComplexEuclidean dimension) lower curve).coeFn_toLp.symm
  have second : slope = collarContinuousL2 (ComplexEuclidean dimension) lower rhs := by
    apply Lp.ext
    exact slopeSame.trans (collarContinuous_memLp (ComplexEuclidean dimension) lower rhs).coeFn_toLp.symm
  rw [first,second]
  exact collarWeakDerivative_of_closedClassical lower bounded curve rhs derivative

end Grad.AnnularOriginalSmoothCore
