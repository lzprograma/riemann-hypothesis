module

import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIterated
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open MeasureTheory Set
open UpperHalfPlane hiding I

private theorem pt_re_im (x y : ℝ) (hy : 0 < y) :
    (UpperTheory.V.Af.Rs.pt x y).re = x ∧ (UpperTheory.V.Af.Rs.pt x y).im = y := by
  rw [UpperTheory.V.Af.Rs.pt, ← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im,
    UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private theorem volume_restrict_strip_eq_map_withDensity (hV : UpperTheory.V.Af.Rs.VolMap) :
    (volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip =
      Measure.map (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  apply _root_.GlobalTheory.EisM.restrict_strip_eq_map <;> assumption

theorem UpperTheory.V.Af.Rs.stripIm :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripIm := by
  intro hV φ hφ hint
  have hf : Measurable fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have him : Continuous fun z : ℍ => z.im := Complex.continuous_im.comp UpperHalfPlane.continuous_coe
  have hm : Measurable fun z : ℍ => φ z.im := hφ.comp him.measurable
  show Integrable (fun z : ℍ => φ z.im) ((volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip)
  rw [volume_restrict_strip_eq_map_withDensity hV, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt]
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1)) := integrable_const 1
  have h2 : Integrable (fun y => φ y / y ^ 2) (volume.restrict (Ioi (0:ℝ))) := hint
  refine (h1.mul_prod h2).congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
    with p hp
  simp only [Function.comp_apply, (pt_re_im p.1 p.2 hp).2,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / p.2 ^ 2), smul_eq_mul, one_mul]
  ring
