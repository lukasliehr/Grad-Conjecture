import AKC3ConjugatedGradeCoherence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 250000
open Set
open scoped Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.BoundaryLift Grad.SourceCollarCoefficients

/-- Coherence means the grade is a coordinate choice for the SAME operator. -/
def GradeCoherentOn {source target : ℕ} (parameters : PhaseParameters) (domain : Set ℝ)
    (action : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target) : Prop :=
  ∀ grade reserve radius, radius ∈ domain →
    (action grade radius).comp (hilbertReserve parameters source reserve) =
      (hilbertReserve parameters target reserve).comp (action (grade + reserve) radius)

/-- Each requested finite radial order is proved at the original width using
a finite polynomial input reserve. No same-grade C∞ conclusion is built in. -/
def FiniteGradeSmooth {source target : ℕ} (parameters : PhaseParameters) (domain : Set ℝ)
    (action : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target) : Prop :=
  ∀ grade order : ℕ, ∃ reserve : ℕ, ContDiffOn ℝ order
    (fun radius => (action grade radius).comp (hilbertReserve parameters source reserve)) domain

theorem contDiffOn_operatorComposition {source middle target : ℕ} {order : WithTop ℕ∞}
    {domain : Set ℝ} {outer : ℝ → CellL2 middle →L[ℂ] CellL2 target}
    {inner : ℝ → CellL2 source →L[ℂ] CellL2 middle}
    (one : ContDiffOn ℝ order outer domain) (two : ContDiffOn ℝ order inner domain) :
    ContDiffOn ℝ order (fun radius => (outer radius).comp (inner radius)) domain :=
  ((ContinuousLinearMap.compL ℂ (CellL2 source) (CellL2 middle) (CellL2 target)).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂_contDiffOn one two

theorem gradeCoherent_reservedComposition {source middle target : ℕ}
    (parameters : PhaseParameters) (domain : Set ℝ)
    (outer : ℕ → ℝ → CellL2 middle →L[ℂ] CellL2 target)
    (inner : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 middle)
    (coherent : GradeCoherentOn parameters domain inner)
    (grade first second : ℕ) (radius : ℝ) (inside : radius ∈ domain) :
    ((outer grade radius).comp (inner grade radius)).comp (hilbertReserve parameters source (first + second)) =
      ((outer grade radius).comp (hilbertReserve parameters middle first)).comp
        ((inner (grade + first) radius).comp (hilbertReserve parameters source second)) := by
  apply ContinuousLinearMap.ext
  intro field
  rw [hilbertReserve_add]
  exact congrArg (outer grade radius)
    (congrArg (fun mapping : CellL2 source →L[ℂ] CellL2 middle => mapping (hilbertReserve parameters source second field))
      (coherent grade first radius inside))

theorem FiniteGradeSmooth.comp {source middle target : ℕ} {parameters : PhaseParameters} {domain : Set ℝ}
    {outer : ℕ → ℝ → CellL2 middle →L[ℂ] CellL2 target}
    {inner : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 middle}
    (one : FiniteGradeSmooth parameters domain outer) (two : FiniteGradeSmooth parameters domain inner)
    (coherent : GradeCoherentOn parameters domain inner) :
    FiniteGradeSmooth parameters domain (fun grade radius => (outer grade radius).comp (inner grade radius)) := by
  intro grade order
  obtain ⟨first, firstSmooth⟩ := one grade order
  obtain ⟨second, secondSmooth⟩ := two (grade + first) order
  refine ⟨first + second, (contDiffOn_operatorComposition firstSmooth secondSmooth).congr ?_⟩
  intro radius inside
  exact gradeCoherent_reservedComposition parameters domain outer inner coherent grade first second radius inside

/-- Composing with a fixed reserve is a genuine continuous linear map on
operator space, so ordinary real differentiation applies directly. -/
def reserveOperator {source target : ℕ} (parameters : PhaseParameters) (reserve : ℕ) :
    (CellL2 source →L[ℂ] CellL2 target) →L[ℝ] (CellL2 source →L[ℂ] CellL2 target) :=
  ((ContinuousLinearMap.compL ℂ (CellL2 source) (CellL2 source) (CellL2 target)).flip
    (hilbertReserve parameters source reserve)).restrictScalars ℝ

theorem hasDerivWithinAt_reserve {source target : ℕ} (parameters : PhaseParameters) (reserve : ℕ)
    {domain : Set ℝ} {action : ℝ → CellL2 source →L[ℂ] CellL2 target}
    {derivative : CellL2 source →L[ℂ] CellL2 target} {radius : ℝ}
    (differentiable : HasDerivWithinAt action derivative domain radius) :
    HasDerivWithinAt (fun point => (action point).comp (hilbertReserve parameters source reserve))
      (derivative.comp (hilbertReserve parameters source reserve)) domain radius :=
  (reserveOperator (source := source) (target := target) parameters reserve).hasFDerivAt.comp_hasDerivWithinAt radius differentiable

/-- The derivative of a finite-grade smooth family is again finite-grade
smooth, assuming only its genuine unreserved first derivative exists. -/
theorem FiniteGradeSmooth.derivative {source target : ℕ} {parameters : PhaseParameters} {domain : Set ℝ}
    {action : ℕ → ℝ → CellL2 source →L[ℂ] CellL2 target}
    (smooth : FiniteGradeSmooth parameters domain action) (unique : UniqueDiffOn ℝ domain)
    (differentiable : ∀ grade, DifferentiableOn ℝ (action grade) domain) :
    FiniteGradeSmooth parameters domain (fun grade => derivWithin (action grade) domain) := by
  intro grade order
  obtain ⟨reserve, regular⟩ := smooth grade (order + 1)
  have next : ContDiffOn ℝ order
      (derivWithin (fun radius => (action grade radius).comp (hilbertReserve parameters source reserve)) domain) domain :=
    ContDiffOn.derivWithin (m := (order : WithTop ℕ∞)) regular unique (by simp)
  refine ⟨reserve, next.congr ?_⟩
  intro radius inside
  exact (hasDerivWithinAt_reserve parameters reserve (differentiable grade radius inside).hasDerivWithinAt).derivWithin
    (unique radius inside) |>.symm

end Grad.AnnularWeightedSmoothness
