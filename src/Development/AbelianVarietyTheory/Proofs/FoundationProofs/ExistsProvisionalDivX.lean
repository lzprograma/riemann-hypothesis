module

public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Formalism.LocalRingCardinality.DataKap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX, Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX", "h": "module\n\npublic import Formalism.LocalRingCardinality.DataDIV\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory

def provisionalShimX (Tau : Type) [Fintype Tau] (N j : ℕ) (lev : Finset ℕ) (hj : 1 ≤ j)
    (hjN : j < N) (hlev : ∀ p ∈ lev, p.Prime) : DV.ShimX Tau where
  N := N
  j := j
  j_pos := hj
  j_lt := hjN
  lev := lev
  lev_prime := hlev
  Comp := Unit
  vol := 0
  chern := 0
  chern_homog := fun _ _ _ _ => rfl
  arDeg := fun _ _ => 0
  arDeg_homog := fun _ _ _ _ _ _ => rfl
  arMix := fun _ _ _ => 0
  arMix_HT := fun _ _ _ _ => rfl
  arMix_DR := fun _ _ _ _ => rfl
  CurveHT := fun _ => Empty
  degHT := fun _ _ _ => 0
  CurveDR := fun _ => Empty
  degDR := fun _ _ _ => 0
  FibComp := fun _ => Empty
  fibInBd := fun _ _ => False
  Pt := Unit
  phiDR := fun _ _ _ => 0
  phiMod := fun _ _ _ => 0
  phiFr := fun _ _ _ => 0
  XC := Unit
  rfn := fun _ => Real.exp 1
  rfn_ge := fun _ => le_rfl
  hLo := fun _ => 1
  hUp := fun _ => 1
  hLo_le := fun _ => ⟨one_pos, le_rfl⟩
  connN := fun _ => 0
  curvN := fun _ => 0
  compOf := fun _ => ()
  normDetInf := fun _ _ => 1
  compPt := fun _ => ()
  normDetT := fun _ _ _ => 1
  normDetH := fun _ _ _ => 1
  htDetT := fun _ _ _ => 0
  ALB := Unit
  arSelf := fun _ => 0
  arSelfC := fun _ _ => 0
  arSelf_sum := fun _ => by simp
  geo := fun _ => 0
  geoC := fun _ _ => 0
  geo_sum := fun _ => by simp
  arVol := fun _ => 0
  semipos := fun _ => True
  nefFib := fun _ => True
  arNef := fun _ => True
  Mbar := fun _ _ _ => ()

end GlobalTheory

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX", "h": "module\n\npublic import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX\npublic import Formalism.LocalRingCardinality.DataKap\nimport Formalism.LocalRingCardinality.RankBoundMonotoneInDimension\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions NumberField

noncomputable section

namespace GlobalTheory.ProvisionalDivX

structure MjForm (D : D7) (j : ℕ) where

  H : HLat D.what₂.LL

  jm : H.V →ₛₗ[D.what₂.embLL] D.what₂.Mj j
  good : H.Good
  basis : LinearIndependent ℂ (fun i => jm (H.b i)) ∧
    Submodule.span ℂ (Set.range (fun i => jm (H.b i))) = ⊤
  lat : 1 ≤ j → j ≤ D.R.m → ∀ x, x ∈ H.L ↔ ∃ c : D.what₂.Mj j → 𝓞 D.what₂.LL,
    jm x = ∑ v ∈ (D.what₂.MjLat j).gen, D.what₂.embLL ((c v : 𝓞 D.what₂.LL) : D.what₂.LL) • v
  sub : 1 ≤ j → j ≤ D.R.m → ∀ x ∈ (D.what₂.MjLat j).gen, x ∈ Set.range jm

theorem resChar_eq_iff (D : D7) {p : ℕ} (hp : p.Prime) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = p ↔ (p : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  constructor
  · intro h; rw [← h]; exact resChar_mem D w
  · intro hmem
    by_contra hne
    have hcop : Nat.Coprime (D.what₂.places.resChar w) p :=
      (Nat.coprime_primes (D.what₂.places.resChar_prime w) hp).mpr hne
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (p : 𝓞 D.what₂.LL) :=
      hcop.cast
    apply (D.plEq w).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem D w)) (Ideal.mul_mem_left _ _ hmem)

def placeEquiv (D : D7) (p : ℕ) [hp : Fact p.Prime] :
    Formalism.L2.Geo.PlL D p ≃ {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (resChar_eq_iff D hp.out)).symm

def smallShim (D : D7) (r : ℕ) : DV.ShimX D.what₂.Tau :=
  provisionalShimX D.what₂.Tau (max r 2) 1 ∅ le_rfl (by omega) (by simp)

end GlobalTheory.ProvisionalDivX

namespace GlobalTheory

open ProvisionalDivX

def provisionalDivX (D : D7) (G : DV.Geo D.what₂.LL) (Y : G.Var)
    (jc : ∀ (p : ℕ) [Fact p.Prime], DV.KW p →+* ℂ)
    (F : ∀ j, MjForm D j) : DivX D :=
  letI := D.host.cmStar
  { geo := G
    Lev := Unit
    levPr := fun _ => ∅
    shv := fun S _ => smallShim D S.rank
    PlP := fun p _ => Formalism.L2.Geo.PlL D p
    plpFin := fun p _ => Formalism.L2.Geo.finPl D p
    wtP := fun p _ => Formalism.L2.Geo.wtL D p
    plP := fun p _ => placeEquiv D p
    jC := fun p _ _ => jc p
    Mp := fun _ _ _ _ _ => Unit
    vdd := fun _ _ => 0
    CurveM := fun _ _ _ _ _ _ => Empty
    degM := fun _ _ _ _ _ _ _ _ => 0
    htMdl := fun _ _ _ _ _ => ()
    htCurve := fun _ _ p _ =>
      { toFun := fun c => Empty.elim c
        invFun := fun c => c.2
        left_inv := fun c => Empty.elim c
        right_inv := fun c => Empty.elim c.2 }
    MjH := fun j => (F j).H
    MjH_good := fun j => (F j).good
    jM := fun j => (F j).jm
    jM_basis := fun j => (F j).basis
    jM_lat := fun j => (F j).lat
    MjLat_sub := fun j => (F j).sub
    Qp := fun _ => ∅
    degreeZero_partial_set_empty := rfl
    Qp_muAt := fun _ => Finset.notMem_empty _
    QPl := fun _ => Empty
    qv := fun _ v => v.elim
    Comp := fun _ => Unit
    Yv := fun _ _ => Y
    Lw := fun _ _ => 0
    iMj := fun _ _ => 0
    logLam := fun j σ _ => Real.log (D.what₂.lamP D.what₂.mu0 j σ)
    logLam_base := fun _ _ => rfl
    kapR := fun _ => kapSharp D
    Surf := Empty
    SurfFp := Empty }

end GlobalTheory

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX =====
