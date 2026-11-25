module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.G8

open scoped Classical

noncomputable section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def sing (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool) :
    ∀ v : Pl E, Bool → GLw n v → ℂ :=
  Function.update (fun v _ => (N v : Set (GLw n v)).indicator 1) w
    (fun b => if b = b₀ then f else (N w : Set (GLw n w)).indicator 1)

private theorem sing_self (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool) :
    sing N w f b₀ w b₀ = f := by
  simp [sing]

private theorem sing_ne (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (b₀ : Bool)
    (v : Pl E) (b : Bool) (h : (v, b) ≠ (w, b₀)) :
    sing N w f b₀ v b = (N v : Set (GLw n v)).indicator 1 := by
  by_cases hv : v = w
  · subst hv
    have hb : b ≠ b₀ := fun e => h (by rw [e])
    simp [sing, hb]
  · simp [sing, Function.update_of_ne hv]

private theorem sing_fam (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ)
    (b₀ : Bool) (hs : Sl S (w, b₀)) (hf : IsHecke (N w) f) :
    Fam S N {(w, b₀)} (sing N w f b₀) := by
  refine ⟨fun i hi => ?_, fun i _ hi => ?_⟩
  · rw [Finset.mem_singleton] at hi
    subst hi
    exact ⟨hs, by rw [sing_self]; exact hf⟩
  · exact sing_ne N w f b₀ i.1 i.2 (by simpa using hi)

private theorem sing_cross (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (v : Pl E) :
    sing N w f false v true = sing N w f true v false := by
  rw [sing_ne N w f false v true (by simp), sing_ne N w f true v false (by simp)]

private theorem sing_diag (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E) (f : GLw n w → ℂ) (v : Pl E) :
    sing N w f false v false = sing N w f true v true := by
  by_cases hv : v = w
  · subst hv
    rw [sing_self, sing_self]
  · rw [sing_ne N w f false v false (by simp [hv]), sing_ne N w f true v true (by simp [hv])]

private theorem pf_sing_twist (S : Set (Pl E)) (N : ∀ w : Pl E, Subgroup (GLw n w)) (w : Pl E)
    (f : GLw n w → ℂ) (hw : IsSplitAt w) (hth : ∀ g, thF E n (thF E n g) = g)
    (hin : ∀ v : Pl E, ¬ IsSplitAt v → ∀ g, qw n v true g ∈ KGL v (n := n) ↔ qw n v false g ∈ KGL v (n := n))
    (hN : ∀ v : Pl E, ¬ IsSplitAt v → N v = KGL v (n := n)) (g : GF E n) :
    pf S (sing N w f false) (thF E n g) = pf S (sing N w f true) g := by
  unfold pf
  refine finprod_congr fun v => finprod_congr fun _ => ?_
  have q0 : qw n v false (thF E n g) = qw n v true g := rfl
  have q1 : qw n v true (thF E n g) = qw n v false g := by
    show GeneralLinearGroup.map (pLoc E v) (thF E n (thF E n g)) = _
    rw [hth]
    rfl
  rw [q0, q1]
  by_cases hs : IsSplitAt v
  · rw [ite_eq_left hs, ite_eq_left hs, sing_cross, sing_diag, mul_comm]
  · have hv : v ≠ w := fun e => hs (e ▸ hw)
    rw [ite_eq_right hs, ite_eq_right hs, mul_one, mul_one, sing_ne N w f false v false (by simp [hv]),
      sing_ne N w f true v false (by simp [hv]), hN v hs]
    have h := hin v hs g
    by_cases hm : qw n v false g ∈ KGL v (n := n)
    · rw [Set.indicator_of_mem (show qw n v true g ∈ (KGL v (n := n) : Set (GLw n v)) from h.2 hm),
        Set.indicator_of_mem (show qw n v false g ∈ (KGL v (n := n) : Set (GLw n v)) from hm)]
      rfl
    · rw [Set.indicator_of_notMem (show qw n v true g ∉ (KGL v (n := n) : Set (GLw n v)) from fun e => hm (h.1 e)),
        Set.indicator_of_notMem (show qw n v false g ∉ (KGL v (n := n) : Set (GLw n v)) from hm)]

end SlopeTestRemainingChoices

theorem ySwap_pf : SlotBasic → PfHecke → ProdOp → YSwap := by
  intro hSF hPH hPO E _ _ _ n S Z N hS hZ hG π y w hw f hf x x' hx
  obtain ⟨hth, -, -, -, -, hin, -⟩ := hSF E n S hS
  have hwS := hZ w hw
  have hN : ∀ v : Pl E, ¬ IsSplitAt v → N v = KGL v (n := n) :=
    fun v hv => (hG v).2.2.2 fun hvZ => hv (hZ v hvZ).2
  have F0 := sing_fam S N w f false ⟨hwS.1, by simp⟩ hf
  have F1 := sing_fam S N w f true ⟨hwS.1, fun _ => hwS.2⟩ hf
  have h0 := hPH E n S Z N hS hZ hG _ _ F0
  have h1 := hPH E n S Z N hS hZ hG _ _ F1
  have e : (fun g => pf S (sing N w f false) (thF E n g)) = pf S (sing N w f true) :=
    funext (pf_sing_twist S N w f hwS.2 hth hin hN)
  have t := y.tw _ h0
  rw [e] at t
  have a0 : y.r (pf S (sing N w f false)) x = x' := by
    apply Subtype.ext
    rw [y.act _ h0, hPO E n S Z N hS hZ hG _ _ F0 _ (y.fix x.2), hx]
    simp [sing_self]
  have t' := congrArg (fun T : Module.End ℂ y.Y => T x) t
  simp only [Module.End.mul_apply, a0] at t'
  rw [t', y.act _ h1, hPO E n S Z N hS hZ hG _ _ F1 _ (y.fix (y.A x).2)]
  simp [sing_self]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
