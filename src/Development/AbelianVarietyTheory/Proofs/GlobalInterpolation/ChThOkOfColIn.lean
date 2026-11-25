module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty\npublic import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteQuotOfReps\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire\npublic import Formalism.LocalToGlobal.KernelLattices.ThDistC\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent\npublic import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational\nimport Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg\nimport Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain

noncomputable section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (degAt degNu)

namespace GlobalTheory.ChainTheta

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word)

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) (j : ℕ) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst)
    (hR : RatStep W Ch sel mu cst A u i j) :
    ThDist.Ok (stepC W Ch sel mu cst A u i (W.lamTrue u j)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u)
      ((rhoVr X.emb (W.lamTrue u i)).comp (ufGL X.E (R.N i))) ((rhoVr X.emb (W.lamTrue u j)).comp (ufGL X.E (R.N j)))
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) := by
  have hD := modulus_pos sel mu cst u hT
  unfold RatStep at hR
  rw [← stepC_eq_stepT W Ch sel mu cst hq A u i hi] at hR
  exact
    { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A _ _ sel _ _ _ _ _ _ N fr N' fr' c x x' h
      equiv := thDistC_equiv A _ _ sel _ _ _ _ _ _ hD _ _ hR
      det := fun N fr N' fr' c x κ κ' _ _ =>
        thDistC_det A _ _ sel _ _ _ _ _ _ _ _ (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _)
          (unitInv_rho Ch sel mu i) N fr N' fr' c x κ κ' }

end Chain

theorem chTh_ok_of_hyp {Z : Dat} {H : D7} {s : Seam H Z.X} {cc : Ideal (𝓞 H.host.K)} {δ : ℂ} (B : Base H cc δ) {χ : TaylorLogMetric.IdE H → ℂ}
    {cD : H.what₂.Tau → ℂ} {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
    {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)} {u : Z.Pr.Word} {m2 : ℕ} (hm : Z.R.m = m2 + 2)
    (h : Hyp Z s cc δ χ cD sel S mu cst u) (hE : B.EqP χ) (hV : B.VecP χ) (hq : MuqTie Z.Ch sel mu cst)
    (hJ : ∀ i, i < Z.R.m → ∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x →
      ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (degAt m τ : ℤ) = degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) →
      ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ *
        jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) :
    ChTh.Ok (Ch := Z.Ch) cst (chTh Z.W Z.Ch sel mu cst (ambOf s B χ cD) u m2) := by
  have key : ∀ i j, i < Z.R.m → j = i + 1 →
      ThDist.Ok (stepC Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (Z.W.lamTrue u j)) (Sall sel mu u)
        (cAof sel mu cst * cBof sel mu cst u) ((rhoVr Z.X.emb (Z.W.lamTrue u i)).comp (ufGL Z.X.E (Z.R.N i)))
        ((rhoVr Z.X.emb (Z.W.lamTrue u j)).comp (ufGL Z.X.E (Z.R.N j))) (rhoS Z.Ch sel mu i) (rhoT Z.Ch sel mu i) := by
    rintro i _ hi rfl
    exact stepC_ok_deg Z.W Z.Ch sel mu cst _ u i hi (i + 1) (h.ok.primes.T_prime u).pos hq
      (_root_.GlobalTheory.KerT.RatLaw.ratStep Z H s cc δ B χ cD sel S mu cst u i hi h hE hV hq (hJ i hi))
  exact ⟨fun i hi => key i (i + 1) (by omega) rfl, key (m2 + 1) Z.R.m (by omega) hm⟩


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem chTh_ok_of_colIn (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi)
    (a : I.ι) (u : B.Word) (m2 : ℕ) (hm : B.R.m = m2 + 2) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u m2) := by
  have h1 := chTh_ok_of_hyp (Z := I.dat) (I.J.toRec B C W V S N G) hm (hyp_of_colIn B C W V S N G I h a u) hE hV
    (muqTie_of_ok _ _ _ _ _ (h.idx_ok a)) (by
      rw [← AmbIn.amb_eq_ambOf]
      intro i hi L L' c x hx m hd
      refine hJ.exists_eq hi hx fun τ => ?_
      rw [monoDeg_eq_sum]
      exact (hd τ).trans (GlobalTheory.MoveCompare.degNu_eq (Pr := B.primes X) B.wts u hi τ))
  rw [← AmbIn.amb_eq_ambOf] at h1
  exact h1


open GlobalTheory.Mem GlobalTheory.Mem.Col2 in
theorem chTh_ok_of_colIn' (B : GlobalTheory.Mem.Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (N : NStage B C W)
    (G : GJStage B C) {X : PreX B.toPre} (I : ColIn B X) (h : I.Ok) (hJ : I.JetsIn)
    (hE : (I.J.toRec B C W V S N G).EqP I.chi) (hV : (I.J.toRec B C W V S N G).VecP I.chi) (a : I.ι) (u : B.Word) :
    ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) :=
  chTh_ok_of_colIn B C W V S N G I h hJ hE hV a u _ h.hm

end GlobalTheory.ChainTheta
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn =====
