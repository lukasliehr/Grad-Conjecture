import AKU78RealFiniteLiftAverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.AxisSplit Grad.AxisJet
open Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.GaugeCoefficients.Physical.Allocation

theorem finiteRealCore_vanishing {parameters : PhaseParameters} {dimension depth : ℕ}
    (field : ACore parameters dimension) (vanishes : ∀ cell, VanishingJets depth (field.val cell))
    (cell : ℤ) : VanishingJets depth ((finiteRealCore field).val cell) := by
  intro order smaller word
  change (((closedDerivativeLinear order word).restrictScalars ℝ)
    ((1/2 : ℝ) • (field.val cell+closedJetConjugate (field.val (-cell))))) sourceOrigin = 0
  rw [map_smul,map_add]
  change (1/2 : ℝ) • (closedDerivative (field.val cell) order word sourceOrigin+
    closedDerivative (closedJetConjugate (field.val (-cell))) order word sourceOrigin) = 0
  rw [vanishes cell order smaller word,closedJetConjugate_derivative]
  change (1/2 : ℝ) • (0+cartesianPhysicalConjugation dimension
    (closedDerivative (field.val (-cell)) order word sourceOrigin)) = 0
  rw [vanishes (-cell) order smaller word,map_zero,add_zero,smul_zero]

theorem finiteRealSource_higherVanishing (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (vanishes : SourceHigherVanishing source) : SourceHigherVanishing (finiteRealSource parameters source) := by
  refine ⟨?_,?_,?_⟩
  · intro cell
    rw [finiteRealSource_cartesian]
    exact finiteRealCore_vanishing _ vanishes.1 cell
  · intro cell
    change VanishingJets 2 ((finiteRealCore (source 2)).val cell)
    exact finiteRealCore_vanishing _ vanishes.2.1 cell
  · intro cell
    change VanishingJets 3 ((finiteRealCore (source 3)).val cell)
    exact finiteRealCore_vanishing _ vanishes.2.2 cell

def originalRealFiniteLiftU (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : ACore parameters 3 :=
  finiteRealCore (originalFiniteLiftU parameters length rho epsilon field low source)

def originalRealFiniteLiftS (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : ACore parameters 1 :=
  finiteRealCore (originalFiniteLiftS parameters length rho epsilon field low source)

def originalRealFiniteLiftResidual (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : SmoothQuotient parameters :=
  source - quotientRowsDerivative parameters length 1 ((epsilon : ℂ),planarReferenceCore parameters+field,potential)
    ![(0,originalRealFiniteLiftU parameters length rho epsilon field low source,
      originalRealFiniteLiftS parameters length rho epsilon field low source)]

theorem originalRealFiniteLiftResidual_average (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (potential : ACore parameters 1)
    (currentReal : cartesianCoreConjugation parameters (planarReferenceCore parameters+field) = planarReferenceCore parameters+field)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (sourceReal : zCoreConjugation parameters source = source) :
    originalRealFiniteLiftResidual parameters length rho epsilon field potential low source =
      finiteRealSource parameters (originalFiniteLiftResidual parameters length rho epsilon field potential low source) := by
  unfold originalRealFiniteLiftResidual originalFiniteLiftResidual originalRealFiniteLiftU originalRealFiniteLiftS
  rw [quotientRowsDerivative_etaZero,quotientRowsDerivative_etaZero,
    physicalEtaZeroRows_realAverage parameters length _ (Complex.conj_ofReal epsilon) currentReal,map_sub]
  rw [show finiteRealSource parameters source = source from finiteRealAverage_of_fixed _ source sourceReal]

/-- A genuine real lift has the same actual source cancellation, with no new
Taylor condition on the original source or current. -/
theorem originalRealFiniteLiftResidual_higherVanishing (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (positive : 0 < length) (field : ACore parameters 3) (potential : ACore parameters 1)
    (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (currentReal : cartesianCoreConjugation parameters (planarReferenceCore parameters+field) = planarReferenceCore parameters+field)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (sourceReal : zCoreConjugation parameters source = source) :
    SourceHigherVanishing (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source) := by
  rw [originalRealFiniteLiftResidual_average parameters length rho epsilon field potential currentReal low source sourceReal]
  exact finiteRealSource_higherVanishing parameters _
    (originalFiniteLiftResidual_higherVanishing parameters length rho epsilon positive field potential vanishes low source flat)

end Grad.FinitePhysicalJetLift
