import AKCZ7ShiftedResolventDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Filter Set
open scoped Topology ContDiff
namespace Grad.NashMoser.InverseCalculus

private theorem finite_contDiffOn_linearFunction
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (order : ℕ∞ω) (linear : F → G) (additive : ∀ x y, linear (x+y)=linear x+linear y)
    (scalar : ∀ (r : ℝ) x, linear (r • x)=r • linear x) (continuous : Continuous linear)
    (mapping : E → F) (domain : Set E) (smooth : ContDiffOn ℝ order mapping domain) :
    ContDiffOn ℝ order (fun point => linear (mapping point)) domain := by
  let bundled : F →L[ℝ] G := { toFun := linear, map_add' := additive, map_smul' := scalar, cont := continuous }
  exact bundled.contDiff.comp_contDiffOn smooth

/-- The derivative word is a polynomial in the two shifted inverse factors
and the actual forward derivative. -/
theorem shiftedInverseDerivative_contDiffOn
    {Parameter Input HighState MiddleSource Output : Type*}
    [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [NormedAddCommGroup Input] [NormedSpace ℝ Input]
    [NormedAddCommGroup HighState] [NormedSpace ℝ HighState]
    [NormedAddCommGroup MiddleSource] [NormedSpace ℝ MiddleSource]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]
    (order : ℕ∞ω) (domain : Set Parameter)
    (outer : Parameter → MiddleSource →L[ℝ] Output)
    (derivative : Parameter → Parameter →L[ℝ] (HighState →L[ℝ] MiddleSource))
    (inner : Parameter → Input →L[ℝ] HighState)
    (outerSmooth : ContDiffOn ℝ order outer domain)
    (derivativeSmooth : ContDiffOn ℝ order derivative domain)
    (innerSmooth : ContDiffOn ℝ order inner domain) :
    ContDiffOn ℝ order (fun point => shiftedInverseDerivative (outer point) (derivative point) (inner point)) domain := by
  let left : (MiddleSource →L[ℝ] Output) →L[ℝ] ((Input →L[ℝ] MiddleSource) →L[ℝ] (Input →L[ℝ] Output)) :=
    ContinuousLinearMap.compL ℝ Input MiddleSource Output
  let right : (Input →L[ℝ] HighState) →L[ℝ] ((HighState →L[ℝ] MiddleSource) →L[ℝ] (Input →L[ℝ] MiddleSource)) :=
    (ContinuousLinearMap.compL ℝ Input HighState MiddleSource).flip
  have leftSmooth := finite_contDiffOn_linearFunction order (fun mapping => left mapping)
    (fun x y => left.map_add x y) (fun r x => left.map_smul r x) left.continuous outer domain outerSmooth
  have rightSmooth := finite_contDiffOn_linearFunction order (fun mapping => right mapping)
    (fun x y => right.map_add x y) (fun r x => right.map_smul r x) right.continuous inner domain innerSmooth
  exact (leftSmooth.clm_comp (rightSmooth.clm_comp derivativeSmooth)).neg

/-- Finite-order inverse calculus on a Banach scale with genuine loss. Each
order uses a sufficiently high input grade. The base parameter space is
unchanged, and no same-grade inverse is assumed. -/
theorem finiteLossInverse_contDiffOn
    {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    (State Source : ℕ → Type*)
    [∀ grade, NormedAddCommGroup (State grade)] [∀ grade, NormedSpace ℝ (State grade)]
    [∀ grade, NormedAddCommGroup (Source grade)] [∀ grade, NormedSpace ℝ (Source grade)]
    (domain : Set Parameter) (openDomain : IsOpen domain) (forwardLoss inverseLoss : ℕ)
    (forward : ∀ grade, Parameter → State (grade+forwardLoss) →L[ℝ] Source grade)
    (inverse : ∀ output input, Parameter → Source input →L[ℝ] State output)
    (continuous : ∀ output, ∃ input, output+inverseLoss ≤ input ∧ ContinuousOn (inverse output input) domain)
    (resolvent : ∀ output middle input, output+inverseLoss ≤ middle → middle+forwardLoss+inverseLoss ≤ input →
      ∀ base ∈ domain, ∀ point ∈ domain,
      inverse output input point-inverse output input base =
        -(inverse output middle point).comp ((forward middle point-forward middle base).comp
          (inverse (middle+forwardLoss) input base))) :
    ∀ order : ℕ, (∀ grade, ContDiffOn ℝ order (forward grade) domain) →
      ∀ output, ∃ input, output+inverseLoss ≤ input ∧ ContDiffOn ℝ order (inverse output input) domain := by
  intro order
  induction order with
  | zero =>
    intro smooth output
    obtain ⟨input,ordered,regular⟩ := continuous output
    exact ⟨input,ordered,contDiffOn_zero.mpr regular⟩
  | succ order previous =>
    intro smooth output
    have lower : ∀ grade, ContDiffOn ℝ order (forward grade) domain := fun grade =>
      (smooth grade).of_le (by exact_mod_cast Nat.le_succ order)
    obtain ⟨middle,middleOrdered,outerSmooth⟩ := previous lower output
    obtain ⟨input,inputOrdered,innerSmooth⟩ := previous lower (middle+forwardLoss)
    let derivative := fderiv ℝ (forward middle)
    have derivativeSmooth : ContDiffOn ℝ order derivative domain :=
      (smooth middle).fderiv_of_isOpen openDomain (by simp)
    have wordSmooth := shiftedInverseDerivative_contDiffOn (order : ℕ∞ω) domain
      (inverse output middle) derivative (inverse (middle+forwardLoss) input)
      outerSmooth derivativeSmooth innerSmooth
    refine ⟨input,by omega,?_⟩
    rw [show ((order+1 : ℕ) : ℕ∞ω) = (order : ℕ∞ω)+1 by simp]
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn openDomain.uniqueDiffOn).mpr
    refine ⟨by simp, (fun point => shiftedInverseDerivative (inverse output middle point)
      (derivative point) (inverse (middle+forwardLoss) input point)),wordSmooth,?_⟩
    intro point member
    apply HasFDerivAt.hasFDerivWithinAt
    apply shifted_resolvent_hasFDerivAt (inverse output input) (inverse output middle) (forward middle)
      (inverse (middle+forwardLoss) input point) point
    · filter_upwards [openDomain.mem_nhds member] with other otherMember
      exact resolvent output middle input middleOrdered inputOrdered point member other otherMember
    · exact (outerSmooth.continuousOn point member).continuousAt (openDomain.mem_nhds member)
    · exact ((smooth middle).differentiableOn (by simp) point member).differentiableAt
        (openDomain.mem_nhds member) |>.hasFDerivAt

end Grad.NashMoser.InverseCalculus
