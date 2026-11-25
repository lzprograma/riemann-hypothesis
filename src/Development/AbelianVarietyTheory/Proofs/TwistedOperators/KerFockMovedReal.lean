module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuumStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal", "h": "module\n\npublic import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFiniteDatumVectorThetaFockVacuumStatement\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero\npublic import Formalism.LocalToGlobal.IndefiniteReal.DatumVec\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionNegPairPureTensorFock\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFinitePointPreservesFockVacuumStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder

namespace GlobalTheory.FockReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cartan_eq_one {k : ℕ} {A s : Matrix (Fin k) (Fin k) ℂ} (hA : A.PosDef) (h : IsCartanInv A s) : s = 1 := by
  intros
  apply _root_.GlobalTheory.FockPos.cartan_eq_one <;> assumption

theorem negGA_mem_GinfC (V : HSp D) {g : GA D V} (hg : g ∈ GinfC V) : negGA V g ∈ GinfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GinfC, MonoidHom.mem_ker, finHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

def sgnP : Pair T → ℚ
  | .chi _ _ => -1
  | .core _ => -1
  | _ => 1

def realChar (W : G.Weil) (p : Pair T) (e₁ e₂ : D.what₂.Tau → ℤ) (k : GA D (G.V p.small)) (k' : GA D (G.V p.big)) : ℂ :=
  ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) (G.toPair p k k').1)).det ^ e₂ τ *
    (compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (G.toPair p k k').2)).det ^ e₁ τ

def realSubst (W : G.Weil) (B : VertexFrames G) (p : Pair T) (k : GA D (G.V p.small)) (k' : GA D (G.V p.big)) :
    PolF D (G.pT p).rank (G.pS p).rank →ₐ[ℂ] PolF D (G.pT p).rank (G.pS p).rank :=
  GlobalTheory.CompactHowe.substF
    (fun τ => ((G.onT B p τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pT p) (G.toPair p k k').2) * G.onT B p τ).map (opp p))
    (fun τ => ((((G.onS B p τ)⁻¹ * compAt W.θ τ (Formalism.L2.Theta.mt (G.pS p) (G.toPair p k k').1) * G.onS B p τ)⁻¹)ᵀ).map (opp p))

theorem ker_mul (W : G.Weil) (p : Pair T) (F : WO (G.pS p) (G.pT p) → ℂ) (g k : GA D (G.V p.small))
    (h k' : GA D (G.V p.big)) : W.ker p F (g * k) (h * k') = W.ker p (W.om p (G.toPair p k k') F) g h := by
  have e : G.toPair p (g * k) (h * k') = G.toPair p g h * G.toPair p k k' := by
    cases p <;> simp [GridData.toPair, map_mul]
  unfold GridData.Weil.ker
  rw [e]
  simp only [thetaKO, Prod.mk.eta, map_mul, Module.End.mul_apply]

theorem cart_def {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    exact cartan_eq_one (posDef_grid hL hi (tauE D τ)) (W.cart_is (.grid i D.R.m) (show i ≤ D.R.m ∧ D.R.m ≤ D.R.m from ⟨hi, le_rfl⟩) τ)
  · exact hX.elim
  · exact cartan_eq_one (posDef_top G hX (tauE D τ)) (W.cart_is (.top j) (show j ≤ D.R.m from hX) τ)

theorem om_fockIn {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : VertexFrames G) {p : Pair T} (hp : DefPair D.R.m p)
    (hB : ∀ X, DefNode D.R.m X → ∀ τ, (B X τ)ᴴ * gramAt D (G.V X) τ * B X τ = 1)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f)
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.om p (G.toPair p k k') (fockIn W B p f Q) = realChar W p e₁ e₂ k k' • fockIn W B p f (realSubst W B p k k' Q) := by
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  cases p with
  | top t j =>
    have c1 : W.cart (.top j) = fun _ => 1 := funext (cart_def hL W hn.1)
    have c2 : W.cart (.top (j + 1)) = fun _ => 1 := funext (cart_def hL W hn.2)
    simp only [fockIn, GridData.cartS, GridData.onT, GridData.onS, c1, c2] at hv ⊢
    have := _root_.GlobalTheory.RealFockPos.om_pureTensorO_pos D W.ψ W.θ _ _ _ _ (W.om (.top t j)) hom W.θ_is (B (.top j)) (B (.top (j + 1))) (hB _ hn.1)
      (hB _ hn.2) a b ha hb e₁ e₂ (fun τ => by rw [he₁]; simp [sgnP]) (fun τ => by rw [he₂]; simp [sgnP]) f hf hv k hk k' hk' Q
    simp only [GridData.toPair]
    rw [this]
    rfl
  | chi i j =>
    have c1 : W.cart (.grid (i + 1) j) = fun _ => 1 := funext (cart_def hL W hn.2)
    have c2 : W.cart (.grid i j) = fun _ => 1 := funext (cart_def hL W hn.1)
    simp only [fockIn, GridData.cartS, GridData.onT, GridData.onS, c1, c2] at hv ⊢
    have := _root_.GlobalTheory.FockRealNeg.om_pureTensorO_neg D W.ψ W.θ _ _ _ _ (W.om (.chi i j)) hom W.θ_is (B (.grid (i + 1) j)) (B (.grid i j)) (hB _ hn.2)
      (hB _ hn.1) a b ha hb e₁ e₂ (fun τ => by rw [he₁]; simp [sgnP]; ring) (fun τ => by rw [he₂]; simp [sgnP]; ring) f hf hv
      _ (negGA_mem_GinfC _ hk') k hk Q
    simp only [GridData.toPair]
    rw [this]
    rfl
  | mu t i j => exact hp.elim
  | core i => exact hp.elim

theorem negGA_mem_GfC (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem onb_def {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {X : Node} (hX : DefNode D.R.m X) (τ : D.what₂.Tau) :
    (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ = 1 := by
  have hR : X.InRange D.R.m := by
    rcases X with ⟨i, j⟩ | i | j
    · exact show i ≤ D.R.m ∧ j ≤ D.R.m from ⟨hX.1, hX.2.le⟩
    · exact hX.elim
    · exact hX
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hR τ
  rw [cart_def hL W hX, Matrix.one_mul] at h2
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  calc (W.onb X τ)ᴴ * gramAt D (G.V X) τ * W.onb X τ
      = (W.onb X τ)ᴴ * gramAt D (G.V X) τ * (W.onb X τ * Formalism.REAL.Jm ε) := by rw [← h2]
    _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [← Matrix.mul_assoc, h1]
    _ = 1 := hJ

theorem ker_fockIn_real {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : VertexFrames G) {p : Pair T} (hp : DefPair D.R.m p)
    (hB : ∀ X, DefNode D.R.m X → ∀ τ, (B X τ)ᴴ * gramAt D (G.V X) τ * B X τ = 1)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (f : WO (G.pS p) (G.pT p) → ℂ) (hf : IsThetaFunO W.ψ (G.pS p) (G.pT p) f)
    (hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS p) (G.pT p)) W.θ τ (cplxO (G.cartS W.cart p τ) (G.onT W.cart p τ)) f)
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p (fockIn W B p f Q) (g * k) (h * k') =
      realChar W p e₁ e₂ k k' * W.ker p (fockIn W B p f (realSubst W B p k k' Q)) g h := by
  rw [ker_mul, om_fockIn hL W B hp hB a b ha hb e₁ e₂ he₁ he₂ f hf hv k hk k' hk' Q]
  simp only [GridData.Weil.ker, thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]

theorem ker_fock_moved_real {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) {p : Pair T}
    (hp : DefPair D.R.m p) (d : FinDatum G t p) (hd : S.Z.HasVec d)
    (a b : D.what₂.Tau → ℚ) (ha : ∀ τ, HasInfExp D (G.chrS p) τ (a τ)) (hb : ∀ τ, HasInfExp D (G.chrT p) τ (b τ))
    (e₁ e₂ : D.what₂.Tau → ℤ) (he₁ : ∀ τ, (e₁ τ : ℚ) = a τ + sgnP p * (G.pS p).rank / 2)
    (he₂ : ∀ τ, (e₂ τ : ℚ) = -(b τ + sgnP p * (G.pT p).rank / 2))
    (k : GA D (G.V p.small)) (hk : k ∈ GinfC (G.V p.small)) (k' : GA D (G.V p.big)) (hk' : k' ∈ GinfC (G.V p.big))
    (Q : PolF D (G.pT p).rank (G.pS p).rank) (g : GA D (G.V p.small)) (h : GA D (G.V p.big)) :
    W.ker p (W.fock p (GlobalTheory.RowClaim.movedVec t S d) Q) (g * k) (h * k') =
      realChar W p e₁ e₂ k k' * W.ker p (W.fock p (GlobalTheory.RowClaim.movedVec t S d) (realSubst W W.onb p k k' Q)) g h := by
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  obtain ⟨h1, h2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z hp d hd
  have mem : (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).1 ∈ GfC (G.pS p) ∧
      (G.toPair p (S.N.u p.small).1 (S.N.u p.big).1).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | mu t i j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
    | core i => exact ⟨negGA_mem_GfC _ (S.N.u _).2, (S.N.u _).2⟩
    | top t j => exact ⟨(S.N.u _).2, (S.N.u _).2⟩
  obtain ⟨h3, h4⟩ := GlobalTheory.FockRealMove.om_fin_fockVac D W.ψ W.θ _ _ _ _ (W.om p) hom W.θ_is _ _ _ h1 h2 _ mem.1 _ mem.2
  exact ker_fockIn_real hL W W.onb hp (fun X hX τ => onb_def hL W hX τ) a b ha hb e₁ e₂ he₁ he₂ _ h3 h4 k hk k' hk' Q g h

end GlobalTheory.FockReal

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal =====
