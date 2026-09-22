import AW3Proof

noncomputable section

open Grad.PDEBootstrap Grad.AnalyticWeights.Calculus

namespace Grad.GaugeCoefficients.Envelope

/-- The closed unit disk used by the original Cartesian gauge construction. -/
def closedDisk : Set Spatial := Metric.closedBall (0 : Spatial) 1

/-- The original-width nonsmooth comparison envelope
`v_n(Y) = exp ((sigma - gamma * ell * |Y|) * |n|)`. -/
def originalEnvelope (sigma gamma ell : ℝ) (cell : ℤ) (point : Spatial) : ℝ :=
  Real.exp ((sigma - gamma * ell * ‖point‖) * |(cell : ℝ)|)

/-- The physical analytic weight `W_n(Y) = exp (Phi_n(ell Y))`. -/
def originalWeight (sigma gamma ell : ℝ) (cell : ℤ) (point : Spatial) : ℝ :=
  physicalWeight sigma gamma ell cell point

/-- The fixed comparison constant furnished by the phase bounds. -/
def phaseConstant (sigma gamma : ℝ) : ℝ := Real.exp (sigma + gamma)

/-- The cell frequency scaled by the physical circle length. -/
def scaledCellWeight (L ell : ℝ) (cell : ℤ) : ℝ :=
  Real.sqrt (1 + ((cell : ℝ) * ell / L) ^ 2)

/-- Exactly the parameter restrictions used by the original-width estimate. -/
def Admissible (L sigma gamma ell : ℝ) : Prop :=
  0 < L ∧ 0 < gamma ∧ gamma < min 1 sigma ∧ 0 < ell ∧ ell ≤ min 1 L

def EnvelopeGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell →
    ∀ (cell : ℤ) (point : Spatial), point ∈ closedDisk →
      1 ≤ originalEnvelope sigma gamma ell cell point ∧
        originalEnvelope sigma gamma ell cell point ≤ originalWeight sigma gamma ell cell point ∧
          originalWeight sigma gamma ell cell point ≤
            phaseConstant sigma gamma * originalEnvelope sigma gamma ell cell point

def RatioGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell →
    ∀ (base displacement : ℤ) (point : Spatial), point ∈ closedDisk →
      originalWeight sigma gamma ell (base + displacement) point /
          originalWeight sigma gamma ell base point ≤
        phaseConstant sigma gamma * originalEnvelope sigma gamma ell displacement point

def ScaledTriangleGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell →
    ∀ (first second : ℤ),
      scaledCellWeight L ell (first + second) ≤
        Real.sqrt 2 * scaledCellWeight L ell first * scaledCellWeight L ell second

def ScaledWidthGoal : Prop :=
  ∀ (L sigma gamma ell : ℝ), Admissible L sigma gamma ell →
    ∀ cell : ℤ,
      ell * Grad.CellWeights.cellWeight cell ≤
        max 1 L * scaledCellWeight L ell cell

def BlockGoal : Prop :=
  EnvelopeGoal ∧ RatioGoal ∧ ScaledTriangleGoal ∧ ScaledWidthGoal

end Grad.GaugeCoefficients.Envelope
