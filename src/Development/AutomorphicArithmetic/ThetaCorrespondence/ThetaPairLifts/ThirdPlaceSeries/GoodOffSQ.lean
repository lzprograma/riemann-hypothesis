module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
namespace GlobalTheory.OffSQ
theorem good_off_SQ_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i := by
  intro hL D P X hA _ _ i w hG
  have hlev := X.recR.base.lev
  have hmu : D.nd.mu i = D.what₂.muAt (D.nd.w i) := by
    rcases D.what₂.muAt_or (D.nd.w i) with h | h
    · exact absurd h (D.nd.w_tw i)
    · rw [h, D.nd.mu_w i]
  have hxi := X.recR.tupXi (D.nd.mu i) (Or.inr ⟨D.nd.w i, hmu⟩)
  have hunr : (X.R.xiH (X.tupT (D.nd.mu i))).UnrAt w := by
    by_contra hn
    rcases (hlev.Q_ram _ w).1 hn with h | ⟨PP, hPP, hc⟩
    · exact (hG w (Or.inr h)).1 rfl
    · exact (hG PP (Or.inr hPP)).2 hc
  rw [hxi, D.nd.mu_w i, X.Tp.xi_tw, D.nd.w_l i] at hunr
  have hψ := X.Tp.psi_is (D.nd.w i) (D.nd.w_tw i)
  rw [D.nd.w_l i] at hψ
  set δ := X.R.C.delAt (D.nd.l i) with hδdef
  set ψ := X.Tp.psi (D.nd.w i) with hψdef
  set p := if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde with hpdef
  have hd : IsDelta (H := D.host) p δ := by
    rw [hδdef, hpdef, CharFrame.delAt]
    split_ifs
    exacts [X.R.C.isDel', X.R.C.isDel]
  have hmul : ∀ x, (δ * ψ).loc w x = δ.loc w x * ψ.loc w x := fun _ => rfl
  have hnp : ¬ OverP D.host p w := by
    intro hw
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 : 15 ∣ D.nd.l i ^ a := by
      refine (hd.ine w hw (D.nd.l i ^ a)).1 fun x hx => ?_
      have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
      have h2 : ψ.loc w x ^ (D.nd.l i ^ a) = 1 := by
        have := congrArg (fun ξ : HChar D.host.E => ξ.loc w x) ha
        simpa [HChar.loc] using this
      have h3 : (δ.loc w x * ψ.loc w x) ^ (D.nd.l i ^ a) = 1 := by rw [h1, one_pow]
      rwa [mul_pow, h2, mul_one] at h3
    have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
    have h3 : 3 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1
      (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 : 5 = D.nd.l i := (Nat.prime_dvd_prime_iff_eq (by norm_num) hl).1
      ((show (5 : ℕ).Prime by norm_num).dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  have hng : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hw
    have hs : GlobalTheory.Mem.Chr.SplitsC D.host.E (D.host.g k) := D.nd.g_split k
    rcases (GlobalTheory.BigOn.Inhab.overP_iff (D.host.g_prime k) hs (X.R.C.P.pb_over k) w).1 hw with h | ⟨w', h, hc⟩
    · exact (hG w (Or.inl ((hlev.Pg w).2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).1 rfl
    · exact (hG w' (Or.inl ((hlev.Pg w').2 ⟨k, GlobalTheory.BigOn.Inhab.mem_aboveK.1 h⟩))).2 hc
  refine ⟨fun hS => ?_, fun hQ => ?_⟩
  · rcases ((D.nd.S_def i w).1 hS).1 with h | h | h
    · exact hng 0 h
    · exact hng 1 h
    · exact hnp h
  · rw [P.Q_eq i] at hQ
    refine (hψ.ram w).1 ?_ hQ
    intro x hx
    have h1 : δ.loc w x * ψ.loc w x = 1 := (hmul x).symm.trans (hunr x hx)
    rw [hd.unr w hnp x hx, one_mul] at h1
    exact h1
end GlobalTheory.OffSQ
end
