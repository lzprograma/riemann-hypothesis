module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigRep
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA, ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap, ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.BigCasimir

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Slots

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem ofCoords_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (k : ℕ)
    (f : (Fin k → Fin n × Fin n) → (X →ₗ[ℂ] M)) (x : X) (κ : Fin k → Fin n × Fin n) :
    (ofCoords k f x) κ = f κ x := rfl

theorem mAct_apply (k : ℕ) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    mAct E k a b F κ = E a b (F κ) := rfl

theorem factorAd_apply (k : ℕ) (i : Fin k) (a b : Fin n) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    factorAd k i a b F κ =
      (if (κ i).1 = a then F (Function.update κ i (b, (κ i).2)) else 0) -
        (if (κ i).2 = b then F (Function.update κ i ((κ i).1, a)) else 0) := by
  show (ofCoords k _ F) κ = _
  rw [ofCoords_apply, LinearMap.sub_apply]
  split_ifs <;> rfl

theorem mem_ncV_iff {k : ℕ} {F : Big n k M} : F ∈ ncV ε V k ↔
    ∀ κ : Fin k → Fin n × Fin n, ((∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ ∈ V) ∧
      ((¬ ∀ i, ε (κ i).1 ≠ ε (κ i).2) → F κ = 0) := by
  simp only [ncV, Submodule.mem_iInf, Submodule.mem_comap]
  refine forall_congr' fun κ => ?_
  split_ifs with h <;> simp [h] <;> rfl

theorem factorAd_mem_ncV {k : ℕ} (i : Fin k) {a b : Fin n} (hab : ε a = ε b) {F : Big n k M}
    (hF : F ∈ ncV ε V k) : factorAd k i a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  rcases hx : κ i with ⟨x, y⟩
  simp only [factorAd_apply, hx]
  constructor
  · intro hκ
    have hxy : ε x ≠ ε y := by simpa [hx] using hκ i
    refine Submodule.sub_mem _ ?_ ?_ <;> split_ifs with h <;> try exact Submodule.zero_mem _
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [← hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
    · refine (hF _).1 fun j => ?_
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [hab, ← h]; exact hxy
      · rw [Function.update_of_ne hj]; exact hκ j
  · intro hκ
    push Not at hκ
    obtain ⟨j, hj⟩ := hκ
    have key : ∀ p : Fin n × Fin n, ε p.1 = ε p.2 → (¬ ∀ l, ε ((Function.update κ i p) l).1 ≠
        ε ((Function.update κ i p) l).2) := by
      intro p hp h
      by_cases hji : j = i
      · subst hji; exact h j (by simpa using hp)
      · exact h j (by rw [Function.update_of_ne hji]; exact hj)
    have hxy : j = i → ε x = ε y := by intro hji; subst hji; simpa [hx] using hj
    have hc : ∀ p : Fin n × Fin n, (j = i → ε p.1 = ε p.2) → F (Function.update κ i p) = 0 := by
      intro p hp
      by_cases hji : j = i
      · exact (hF _).2 (key p (hp hji))
      · refine (hF _).2 fun h => h j ?_
        rw [Function.update_of_ne hji]; exact hj
    rw [ite_eq_right_iff.2 ?_, ite_eq_right_iff.2 ?_, sub_zero]
    · intro h; subst h; exact hc _ fun hji => by show ε x = ε a; rw [hxy hji, ← hab]
    · intro h; subst h; exact hc _ fun hji => by show ε b = ε y; rw [← hab, hxy hji]

theorem mAct_mem_ncV (hV : IsKStableSub ε E V) (k : ℕ) {a b : Fin n} (hab : ε a = ε b)
    {F : Big n k M} (hF : F ∈ ncV ε V k) : mAct E k a b F ∈ ncV ε V k := by
  rw [mem_ncV_iff] at hF ⊢
  intro κ
  simp only [mAct_apply]
  exact ⟨fun h => hV a b hab _ ((hF κ).1 h), fun h => by rw [(hF κ).2 h, map_zero]⟩

end Slots

end ReciprocityTheory.ChartRestriction.DS.BigCasimir
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Eigenspace.Triangularizable\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCasA\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigRep\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section OneBAux

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem crossOp_eig_gap_of (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hgap : ∀ {r s : Fin n}, ε r ≠ ε s → (n : ℝ) - 1 < h) {θ : ℝ} {y : Big n 1 M}
    (hy : y ∈ Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) (hy0 : y ≠ 0) :
    (0 < h - n + 1 ∧ h - n + 1 ≤ θ) ∨ (θ ≤ -h - 1 ∧ -h - 1 < 0) := by
  classical
  set S : Submodule ℂ (Big n 1 M) :=
    Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1 with hSdef
  have hfdN : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  have hfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le (inf_le_right : S ≤ ncV ε V 1)
  have hS : IsKStableSub ε (bAct E 1) S := by
    intro a b hab v hv
    rw [Submodule.mem_inf] at hv ⊢
    refine ⟨?_, ncV_kStable hV.2.1 1 a b hab v hv.2⟩
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hc : crossOp ε E 1 0 (bAct E 1 a b v) = bAct E 1 a b (crossOp ε E 1 0 v) :=
      LinearMap.congr_fun (crossOp_comm hE 1 0 hab) v
    rw [hc, hv.1, map_smul]
  have hne : S ≠ ⊥ := fun h0 => hy0 ((Submodule.mem_bot ℂ).1 (h0 ▸ hy))
  obtain ⟨w, hwS, hw0, μ, hμ⟩ :=
    exists_khw (bAct_isGlRep hE 1) (bAct_isKUnitary hU 1) hfd hS hne
  have hwS' := Submodule.mem_inf.1 hwS
  obtain ⟨r, s, hrs, hμeq, h2⟩ := crossOp_khw hE hU hV hwS'.2 hw0 hμ
  have hθw : crossOp ε E 1 0 w = (θ : ℂ) • w := Module.End.mem_eigenspace_iff.1 hwS'.1
  rw [hθw, smul_smul] at h2
  have hc : ((2 : ℂ) * (θ : ℂ)) =
      ((casValK ε μ - n - casValK ε (lowK ε lam) : ℝ) : ℂ) := smul_left_injective ℂ hw0 h2
  have hcR : 2 * θ = casValK ε μ - n - casValK ε (lowK ε lam) := by exact_mod_cast hc
  subst hμeq
  have hgap' := hgap hrs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hne' : r ≠ s := fun h => hrs (congrArg ε h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · left
    have hp := crossVal_pos hmono hh hlt hrs
    constructor <;> linarith
  · right
    have hq := crossVal_neg hmono hh hgt hrs.symm
    constructor <;> linarith

theorem crossOp_eig_gap (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {θ : ℝ} {y : Big n 1 M}
    (hy : y ∈ Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) (hy0 : y ≠ 0) :
    (0 < h - n + 1 ∧ h - n + 1 ≤ θ) ∨ (θ ≤ -h - 1 ∧ -h - 1 < 0) :=
  crossOp_eig_gap_of hE hU hV hmono hh (fun hrs => (gap_gt hrs hbig).2) hy hy0

end OneBAux

end ReciprocityTheory.ChartRestriction.DS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp", "h": "module\n\npublic import Mathlib.Analysis.InnerProductSpace.PiL2\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Permute\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\npublic import Mathlib.Analysis.InnerProductSpace.Spectrum\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigCas\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.BigRep\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpEigGap\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.InnerCrossOpEigEqZero\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.Numerics\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section OneB

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem ncV_one_decomp_of (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hgap : ∀ {r s : Fin n}, ε r ≠ ε s → (n : ℝ) - 1 < h) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) :
    ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, x = xm + xp := by
  have : FiniteDimensional ℂ (ncV ε V 1) := finiteDimensional_ncV hV.1 1
  have hstab : ∀ y ∈ ncV ε V 1, crossOp ε E 1 0 y ∈ ncV ε V 1 :=
    fun y hy => crossOp_mem_ncV hV.2.1 1 0 hy
  let T : Module.End ℂ (ncV ε V 1) := (crossOp ε E 1 0).restrict hstab
  have hT : T.IsSymmetric := fun u v => crossOp_symm hU 1 0 u v
  have htop : (⨆ μ, Module.End.eigenspace T μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.1 hT.orthogonalComplement_iSup_eigenspaces_eq_bot
  have hx' : (⟨x, hx⟩ : ncV ε V 1) ∈ ⨆ μ, Module.End.eigenspace T μ := by
    rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction _
    (motive := fun y : ncV ε V 1 => ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, (y : Big n 1 M) = xm + xp)
    hx' ?_ ⟨0, zero_mem _, 0, zero_mem _, by simp⟩ ?_
  · intro μ y hy
    by_cases hy0 : y = 0
    · exact ⟨0, zero_mem _, 0, zero_mem _, by simp [hy0]⟩
    have hTy : T y = μ • y := Module.End.mem_eigenspace_iff.1 hy
    have hev : Module.End.HasEigenvalue T μ := Module.End.hasEigenvalue_of_hasEigenvector ⟨hy, hy0⟩
    have hμ : ((μ.re : ℝ) : ℂ) = μ := Complex.conj_eq_iff_re.1 (hT.conj_eigenvalue_eq_self hev)
    have hCy : crossOp ε E 1 0 y = ((μ.re : ℝ) : ℂ) • (y : Big n 1 M) := by
      rw [hμ]
      have := congrArg Subtype.val hTy
      simpa [T] using this
    have hyN : (y : Big n 1 M) ∈ Module.End.eigenspace (crossOp ε E 1 0) ((μ.re : ℝ) : ℂ) ⊓ ncV ε V 1 :=
      ⟨Module.End.mem_eigenspace_iff.2 hCy, y.2⟩
    have hy0' : (y : Big n 1 M) ≠ 0 := fun h => hy0 (Subtype.ext h)
    rcases crossOp_eig_gap_of hE hU hV hmono hh hgap hyN hy0' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨0, zero_mem _, y, ?_, by simp⟩
      unfold Wp
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)
    · refine ⟨y, ?_, 0, zero_mem _, by simp⟩
      unfold Wm
      exact Submodule.mem_iSup_of_mem μ.re (Submodule.mem_iSup_of_mem (by linarith) hyN)
  · rintro y z ⟨a, ha, b, hb, hy⟩ ⟨c, hc, d, hd, hz⟩
    refine ⟨a + c, add_mem ha hc, b + d, add_mem hb hd, ?_⟩
    rw [Submodule.coe_add, hy, hz]
    abel

theorem ncV_one_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ ncV ε V 1) :
    ∃ xm ∈ Wm ε E V, ∃ xp ∈ Wp ε E V, x = xm + xp :=
  ncV_one_decomp_of hE hU hV hmono hh
    (fun hrs => (gap_gt hrs hbig).2) hx

theorem Wm_khw_of (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hgap : ∀ {r s : Fin n}, ε r ≠ ε s → (n : ℝ) - 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) (hx0 : x ≠ 0) {ν : Fin n → ℝ}
    (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧ ν = lowK ε lam - root a b := by
  have hxN := Wm_le_ncV hx
  obtain ⟨r, s, hrs, hν', hC2⟩ := crossOp_khw hE hU hV hxN hx0 hν
  have hne : r ≠ s := fun h => hrs (h ▸ rfl)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exfalso
    have hgap' := hgap hrs
    have hcpos := crossVal_pos hmono hh hlt hrs
    rw [← hν'] at hcpos
    have hCx : crossOp ε E 1 0 x =
        (((casValK ε ν - n - casValK ε (lowK ε lam)) / 2 : ℝ) : ℂ) • x := by
      calc crossOp ε E 1 0 x = (1 / 2 : ℂ) • ((2 : ℂ) • crossOp ε E 1 0 x) := by
            rw [smul_smul]; norm_num
        _ = _ := by rw [hC2, smul_smul]; congr 1; push_cast; ring
    have horth : ∀ y ∈ Wm ε E V, inner ℂ y x = 0 := by
      intro y hy
      unfold Wm at hy
      refine Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _)
        (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])
      intro θ y hy
      refine Submodule.iSup_induction _ (motive := fun y => inner ℂ y x = 0) hy ?_ (inner_zero_left _)
        (fun a b ha hb => by rw [inner_add_left, ha, hb, add_zero])
      intro hθ y hy
      exact inner_crossOp_eig_eq_zero hU (ne_of_lt (by linarith)) (Module.End.mem_eigenspace_iff.1 hy.1) hCx
    exact hx0 (inner_self_eq_zero.1 (horth x hx))
  · refine ⟨s, r, hlt, fun h => hrs h.symm, ?_⟩
    rw [hν']
    unfold root
    abel

theorem Wm_khw (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wm ε E V) (hx0 : x ≠ 0) {ν : Fin n → ℝ}
    (hν : IsKHWVec ε (bAct E 1) ν x) :
    ∃ a b : Fin n, a < b ∧ ε a ≠ ε b ∧ ν = lowK ε lam - root a b :=
  Wm_khw_of hE hU hV hmono hh
    (fun hrs => (gap_gt hrs hbig).2) hx hx0 hν

theorem Wp_bound_of (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hgap : ∀ {r s : Fin n}, ε r ≠ ε s → (n : ℝ) - 1 < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
  have key : ∀ s : Finset ℝ, ∀ x ∈ ⨆ θ ∈ s, ⨆ (_ : 0 < θ),
      Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1,
      (h - n + 1) * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; simp at hx; simp [hx]
    | insert a s has ih =>
      intro x hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      by_cases ha : 0 < a
      · rw [iSup_pos ha] at hy
        have hCy : crossOp ε E 1 0 y = (a : ℂ) • y := Module.End.mem_eigenspace_iff.1 hy.1
        have horth : inner ℂ y z = 0 := by
          have hle : (⨆ θ ∈ s, ⨆ (_ : 0 < θ),
              Module.End.eigenspace (crossOp ε E 1 0) (θ : ℂ) ⊓ ncV ε V 1) ≤ (ℂ ∙ y)ᗮ := by
            refine iSup₂_le (fun θ hθ => iSup_le (fun _ => ?_))
            intro w hw
            rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
            exact inner_crossOp_eig_eq_zero hU (by rintro rfl; exact has hθ) hCy
              (Module.End.mem_eigenspace_iff.1 hw.1)
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hz)
        have horth' : inner ℂ z y = 0 := by rw [inner_eq_zero_symm]; exact horth
        have hnorm : ‖y + z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
          have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y z horth
          rw [sq, sq, sq]; exact this
        have h1 : inner ℂ (crossOp ε E 1 0 z) y = 0 := by
          rw [crossOp_symm hU, hCy, inner_smul_right, horth', mul_zero]
        have hre : RCLike.re (inner ℂ (crossOp ε E 1 0 (y + z)) (y + z)) =
            a * ‖y‖ ^ 2 + RCLike.re (inner ℂ (crossOp ε E 1 0 z) z) := by
          rw [map_add (f := _), inner_add_left, inner_add_right, inner_add_right, h1, hCy, inner_smul_left,
            inner_smul_left, horth, inner_self_eq_norm_sq_to_K]
          simp
          left
          norm_cast
        have hy' : (h - n + 1) * ‖y‖ ^ 2 ≤ a * ‖y‖ ^ 2 := by
          by_cases hy0 : y = 0
          · simp [hy0]
          · rcases crossOp_eig_gap_of hE hU hV hmono hh hgap hy hy0 with ⟨-, h2⟩ | ⟨h2, h3⟩
            · exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
            · exfalso; linarith
        rw [hnorm, hre]
        nlinarith [ih z hz, hy']
      · rw [iSup_neg ha] at hy
        rw [(Submodule.mem_bot ℂ).1 hy, zero_add]
        exact ih z hz
  unfold Wp at hx
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  have := key s x hs
  linarith

theorem Wp_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h) {x : Big n 1 M} (hx : x ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖x‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E 1 0 x) x) :=
  Wp_bound_of hE hU hV hmono hh
    (fun hrs => (gap_gt hrs hbig).2) hx

end OneB

end ReciprocityTheory.ChartRestriction.DS
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.NcVOneDecomp =====
