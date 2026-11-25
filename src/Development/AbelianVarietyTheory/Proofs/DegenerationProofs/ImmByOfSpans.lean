module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionBySectionsOfSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical

namespace GlobalTheory.ZH

theorem immBy_of_spans (hA : AmpleSt) {R : Type} [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) {N : ℕ}
    (hN : 4 ≤ N) {J : Type} [Fintype J] (s : J → LB.Sec (LPow P.A P.L N (baseOver (Sp R))))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L N (baseOver (Sp R))), ∃ c : J → Γ((baseOver (Sp R)).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j) :
    ImmBy (baseOver (Sp R) ⊗ P.A).hom (LPow P.A P.L N (baseOver (Sp R))) s Set.univ := by
  have := P.isAb.proper
  have hT : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  have hL : IsLocallyNoetherian (Sp R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of R)))
  have key := (AmpleSpan.embedsBy_of_isPullback P.A P.isLB (hA _ P N hN).2 (isAffineOpen_top (Sp R))
    (g := (baseOver (Sp R)).hom ≫ (Sp R).topIso.inv) (φ := (snd (baseOver (Sp R)) P.A).left)
    (f' := (fst (baseOver (Sp R)) P.A).left) (K := Fin 1) (ε := fun _ => (N : ℤ))
    (by rw [AmpleSpan.comp_topIso_inv_ι]; exact (IsPullback.of_hasPullback _ P.A.hom).flip) (by simp) s
    (fun σ => hs σ)).1
  have e : (baseOver (Sp R) ⊗ P.A).hom = (fst (baseOver (Sp R)) P.A).left :=
    (Over.w (fst (baseOver (Sp R)) P.A)).symm.trans (Category.comp_id _)
  rw [SpanImm.immBy_iff, e]
  exact key

theorem ThetaSys.Real.immBy_basis : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ImmBy (baseOver (Sp S.R) ⊗ ρ.P.A).hom (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))) ρ.s Set.univ := by
  intro hL o Ω _ _ _ _ S ρ
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have hN : 4 ≤ S.N := by
    have h : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]
    exact Nat.pow_le_pow_left h 2
  exact immBy_of_spans hL.1.ample ρ.P hN ρ.s fun σ => (ρ.s_basis σ).exists

end GlobalTheory.ZH
