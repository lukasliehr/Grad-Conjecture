import AKC4FiniteGradeOperatorCalculus
import AKC5ReservedResolventDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients

private theorem contDiffOn_spanSingleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {domain : Set ℝ} {order : WithTop ℕ∞} {curve : ℝ → E}
    (regular : ContDiffOn ℝ order curve domain) :
    ContDiffOn ℝ order (fun point => ContinuousLinearMap.toSpanSingleton ℝ (curve point)) domain :=
  ((ContinuousLinearMap.toSpanSingletonLIE ℝ E).contDiff :
    ContDiff ℝ order (ContinuousLinearMap.toSpanSingletonLIE ℝ E)).comp_contDiffOn regular

/-- A reserved forward derivative and exact grade coherence give the
reserved inverse derivative, without unreserved differentiability. -/
theorem coherentInverse_hasDerivWithinAt (parameters : PhaseParameters) (dimension : ℕ) (domain : Set ℝ)
    (forward inverse : ℕ → ℝ → CellL2 dimension →L[ℂ] CellL2 dimension)
    (right : ∀ grade point, point ∈ domain → (forward grade point).comp (inverse grade point) = ContinuousLinearMap.id ℂ _)
    (left : ∀ grade point, point ∈ domain → (inverse grade point).comp (forward grade point) = ContinuousLinearMap.id ℂ _)
    (coherent : GradeCoherentOn parameters domain inverse)
    (grade reserve : ℕ) (base : ℝ) (inside : base ∈ domain)
    (derivative : CellL2 dimension →L[ℂ] CellL2 dimension)
    (continuous : ContinuousWithinAt (inverse grade) domain base)
    (differentiable : HasDerivWithinAt
      (fun point => (forward grade point).comp (hilbertReserve parameters dimension reserve)) derivative domain base) :
    HasDerivWithinAt
      (fun point => (inverse grade point).comp (hilbertReserve parameters dimension reserve))
      (-(inverse grade base).comp derivative |>.comp (inverse (grade + reserve) base)) domain base :=
  reservedInverse_hasDerivWithinAt domain (forward grade) (inverse grade)
    (hilbertReserve parameters dimension reserve) (inverse (grade + reserve) base) derivative base
    (right grade base inside) (left grade) (coherent grade reserve base inside) continuous differentiable

/-- Distributing a left reserve preserves the actual differentiated curve. -/
theorem coherentForward_leftReserve (parameters : PhaseParameters) (dimension : ℕ) (domain : Set ℝ)
    (forward : ℕ → ℝ → CellL2 dimension →L[ℂ] CellL2 dimension)
    (coherent : GradeCoherentOn parameters domain forward) (grade first second : ℕ)
    (base : ℝ) (inside : base ∈ domain) (derivative : CellL2 dimension →L[ℂ] CellL2 dimension)
    (differentiable : HasDerivWithinAt
      (fun point => (forward (grade + first) point).comp (hilbertReserve parameters dimension second)) derivative domain base) :
    HasDerivWithinAt
      (fun point => (forward grade point).comp (hilbertReserve parameters dimension (first + second)))
      ((hilbertReserve parameters dimension first).comp derivative) domain base := by
  let leftCompose : (CellL2 dimension →L[ℂ] CellL2 dimension) →L[ℝ] (CellL2 dimension →L[ℂ] CellL2 dimension) :=
    ((ContinuousLinearMap.compL ℂ (CellL2 dimension) (CellL2 dimension) (CellL2 dimension))
      (hilbertReserve parameters dimension first)).restrictScalars ℝ
  have derived := leftCompose.hasFDerivAt.comp_hasDerivWithinAt base differentiable
  have same (point : ℝ) (h : point ∈ domain) :
      (forward grade point).comp (hilbertReserve parameters dimension (first + second)) =
      leftCompose ((forward (grade + first) point).comp (hilbertReserve parameters dimension second)) := by
    rw [hilbertReserve_add]
    exact (congrArg (fun mapping : CellL2 dimension →L[ℂ] CellL2 dimension =>
      mapping.comp (hilbertReserve parameters dimension second)) (coherent grade first point h))
  apply derived.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with point h
    exact same point h
  · exact same base inside

/-- Finite-order scale-resolvent induction for the SAME two-sided inverse.
Only continuity after some finite reserve is required at order zero. -/
theorem FiniteGradeSmooth.inverse (parameters : PhaseParameters) (dimension : ℕ) (domain : Set ℝ)
    (unique : UniqueDiffOn ℝ domain)
    (forward inverse : ℕ → ℝ → CellL2 dimension →L[ℂ] CellL2 dimension)
    (right : ∀ grade point, point ∈ domain → (forward grade point).comp (inverse grade point) = ContinuousLinearMap.id ℂ _)
    (left : ∀ grade point, point ∈ domain → (inverse grade point).comp (forward grade point) = ContinuousLinearMap.id ℂ _)
    (inverseCoherent : GradeCoherentOn parameters domain inverse)
    (continuous : ∀ grade, ∃ reserve, ContinuousOn
      (fun point => (inverse grade point).comp (hilbertReserve parameters dimension reserve)) domain)
    (smooth : FiniteGradeSmooth parameters domain forward) :
    FiniteGradeSmooth parameters domain inverse := by
  intro grade order
  induction order generalizing grade with
  | zero =>
      obtain ⟨reserve, regular⟩ := continuous grade
      exact ⟨reserve, contDiffOn_zero.mpr regular⟩
  | succ order previous =>
      obtain ⟨first, firstSmooth⟩ := previous grade
      obtain ⟨middle, forwardSmooth⟩ := smooth (grade + first) (order + 1)
      obtain ⟨last, lastSmooth⟩ := previous (grade + first + middle)
      let differentiated := derivWithin
        (fun point => (forward (grade + first) point).comp (hilbertReserve parameters dimension middle)) domain
      have derivativeSmooth : ContDiffOn ℝ order differentiated domain :=
        ContDiffOn.derivWithin (m := (order : WithTop ℕ∞)) forwardSmooth unique (by simp)
      let derivativeCurve := fun point =>
        -(((inverse grade point).comp (hilbertReserve parameters dimension first)).comp
          (differentiated point)).comp
            ((inverse (grade + first + middle) point).comp (hilbertReserve parameters dimension last))
      have derivativeCurveSmooth : ContDiffOn ℝ order derivativeCurve domain :=
        (contDiffOn_operatorComposition (contDiffOn_operatorComposition firstSmooth derivativeSmooth) lastSmooth).neg
      refine ⟨first + middle + last, ?_⟩
      rw [Nat.cast_add, Nat.cast_one,
        contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn unique]
      refine ⟨by simp, (fun point => ContinuousLinearMap.toSpanSingleton ℝ (derivativeCurve point)), ?_, ?_⟩
      · exact contDiffOn_spanSingleton derivativeCurveSmooth
      · intro point h
        have middleDerivative : HasDerivWithinAt
            (fun radius => (forward (grade + first) radius).comp (hilbertReserve parameters dimension middle))
            (differentiated point) domain point :=
          (forwardSmooth.differentiableOn (by simp) point h).hasDerivWithinAt
        have leftContinuous : ContinuousWithinAt
            (fun radius => (hilbertReserve parameters dimension first).comp (inverse (grade + first) radius)) domain point := by
          apply (firstSmooth.continuousOn point h).congr_of_eventuallyEq
          · filter_upwards [self_mem_nhdsWithin] with radius hr
            exact (inverseCoherent grade first radius hr).symm
          · exact (inverseCoherent grade first point h).symm
        have inverseDerivative := leftReservedInverse_hasDerivWithinAt domain
          (forward (grade + first)) (inverse (grade + first))
          (hilbertReserve parameters dimension first) (hilbertReserve parameters dimension middle)
          (inverse (grade + first + middle) point) (differentiated point) point
          (right (grade + first) point h) (left (grade + first))
          (inverseCoherent (grade + first) middle point h) leftContinuous middleDerivative
        have shifted : HasDerivWithinAt
            (fun radius => (inverse grade radius).comp (hilbertReserve parameters dimension (first + middle)))
            (-((inverse grade point).comp (hilbertReserve parameters dimension first)).comp
              (differentiated point) |>.comp (inverse (grade + first + middle) point)) domain point := by
          have value := inverseCoherent grade first point h
          change (inverse grade point) * (hilbertReserve parameters dimension first) =
            (hilbertReserve parameters dimension first) * inverse (grade + first) point at value
          rw [← value] at inverseDerivative
          apply inverseDerivative.congr_of_eventuallyEq
          · filter_upwards [self_mem_nhdsWithin] with radius hr
            change (inverse grade radius).comp (hilbertReserve parameters dimension (first + middle)) =
              ((hilbertReserve parameters dimension first).comp (inverse (grade + first) radius)).comp
                (hilbertReserve parameters dimension middle)
            rw [← inverseCoherent grade first radius hr, hilbertReserve_add, ContinuousLinearMap.comp_assoc]
          · change (inverse grade point).comp (hilbertReserve parameters dimension (first + middle)) =
              ((hilbertReserve parameters dimension first).comp (inverse (grade + first) point)).comp
                (hilbertReserve parameters dimension middle)
            rw [← inverseCoherent grade first point h, hilbertReserve_add, ContinuousLinearMap.comp_assoc]
        have reserved := hasDerivWithinAt_reserve parameters last shifted
        have same : HasDerivWithinAt
            (fun radius => (inverse grade radius).comp (hilbertReserve parameters dimension (first + middle + last)))
            (derivativeCurve point) domain point := by
          simpa only [hilbertReserve_add, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.neg_comp,
            Nat.add_assoc, derivativeCurve] using reserved
        exact same.hasFDerivWithinAt

end Grad.AnnularWeightedSmoothness
