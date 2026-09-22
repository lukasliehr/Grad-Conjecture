import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.Real.Sign

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace Grad.DiskExtension.Seeley

def node (index : ℕ) : ℝ := (2 : ℝ) ^ index

def finiteCoefficient (cutoff index : ℕ) : ℝ :=
  if index ≤ cutoff then
    ∏ other ∈ (Finset.range (cutoff + 1)).erase index,
      (1 + node other) / (node other - node index)
  else 0

def gaussian (index : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((index : ℝ) * ((index : ℝ) + 1) / 2))

def coefficientBound (index : ℕ) : ℝ := Real.exp 6 * gaussian index

def momentMajorant (order index : ℕ) : ℝ := coefficientBound index * node index ^ order

def amplitude (index : ℕ) : ℝ :=
  ⨆ offset : ℕ, |finiteCoefficient (index + offset) index|

def coefficient (index : ℕ) : ℝ := (-1 : ℝ) ^ index * amplitude index

def absoluteMoment (order : ℕ) : ℝ := ∑' index, |coefficient index| * node index ^ order

def GeometryGoal : Prop :=
  (∀ index, 1 ≤ node index ∧ 0 < node index) ∧
  StrictMono node ∧
  (∀ first second, first ≠ second → node first - node second ≠ 0)

def FiniteGoal : Prop :=
  (∀ cutoff index, cutoff < index → finiteCoefficient cutoff index = 0) ∧
  finiteCoefficient 0 0 = 1 ∧
  (∀ cutoff index, index ≤ cutoff →
    finiteCoefficient cutoff index =
      (Lagrange.basis (Finset.range (cutoff + 1)) (fun other => -node other) index).eval 1) ∧
  (∀ cutoff index, index ≤ cutoff →
    0 < (-1 : ℝ) ^ index * finiteCoefficient cutoff index) ∧
  (∀ cutoff index, index ≤ cutoff →
    finiteCoefficient (cutoff + 1) index = finiteCoefficient cutoff index *
      ((1 + node (cutoff + 1)) / (node (cutoff + 1) - node index)))

def FiniteMomentGoal : Prop :=
  (∀ (cutoff : ℕ) (polynomial : Polynomial ℝ), polynomial.natDegree ≤ cutoff →
    ∑ index ∈ Finset.range (cutoff + 1),
      finiteCoefficient cutoff index * polynomial.eval (-node index) = polynomial.eval 1) ∧
  (∀ cutoff order, order ≤ cutoff →
    ∑ index ∈ Finset.range (cutoff + 1),
      finiteCoefficient cutoff index * (-node index) ^ order = 1)

def UniformGoal : Prop :=
  (∀ cutoff index,
    |finiteCoefficient cutoff index| ≤
      Real.exp 6 * (2 : ℝ) ^ (-((index : ℝ) * ((index : ℝ) + 1) / 2))) ∧
  (∀ cutoff order index,
    |finiteCoefficient cutoff index * (-node index) ^ order| ≤ momentMajorant order index)

def LimitGoal : Prop :=
  (∀ index, Monotone (fun offset => |finiteCoefficient (index + offset) index|) ∧
    BddAbove (Set.range (fun offset => |finiteCoefficient (index + offset) index|))) ∧
  (∀ index, Tendsto (fun cutoff => finiteCoefficient cutoff index) atTop (𝓝 (coefficient index))) ∧
  (∀ index, |finiteCoefficient index index| ≤ amplitude index ∧
    0 < amplitude index ∧ amplitude index ≤ coefficientBound index) ∧
  (∀ index, |coefficient index| = amplitude index ∧
    Real.sign (coefficient index) = (-1 : ℝ) ^ index ∧ coefficient index ≠ 0) ∧
  (∀ index, |coefficient index| ≤
    Real.exp 6 * (2 : ℝ) ^ (-((index : ℝ) * ((index : ℝ) + 1) / 2)))

def SummabilityGoal : Prop :=
  (∀ order, Summable (momentMajorant order)) ∧
  (∀ order, Summable (fun index => |coefficient index| * node index ^ order)) ∧
  (∀ order, Summable (fun index => coefficient index * (-node index) ^ order)) ∧
  (∀ order, 0 ≤ absoluteMoment order ∧ absoluteMoment order ≤ ∑' index, momentMajorant order index) ∧
  (∀ order, Tendsto (fun cutoff => ∑' index,
    |coefficient (cutoff + index)| * node (cutoff + index) ^ order) atTop (𝓝 0))

def MomentGoal : Prop :=
  (∀ order, Tendsto (fun cutoff => ∑' index,
    finiteCoefficient cutoff index * (-node index) ^ order)
      atTop (𝓝 (∑' index, coefficient index * (-node index) ^ order))) ∧
  (∀ order, HasSum (fun index => coefficient index * (-(2 : ℝ) ^ index) ^ order) 1) ∧
  (∀ order, ∑' index, coefficient index * (-(2 : ℝ) ^ index) ^ order = 1)

def PolynomialGoal : Prop :=
  ∀ polynomial : Polynomial ℝ,
    Summable (fun index => |coefficient index * polynomial.eval (-node index)|) ∧
    HasSum (fun index => coefficient index * polynomial.eval (-node index)) (polynomial.eval 1)

def BlockGoal : Prop :=
  GeometryGoal ∧ FiniteGoal ∧ FiniteMomentGoal ∧ UniformGoal ∧
    LimitGoal ∧ SummabilityGoal ∧ MomentGoal ∧ PolynomialGoal

end Grad.DiskExtension.Seeley
