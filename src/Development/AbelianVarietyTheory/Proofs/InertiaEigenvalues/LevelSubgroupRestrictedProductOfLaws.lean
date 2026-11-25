module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
open GlobalTheory.RawLift
open GlobalTheory.IdemSupport GlobalTheory.LevSplit

namespace GlobalTheory.LevelProduct

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem piece_one {e : A} (he : e * e = e) : piece he (1 : GL n A) = 1 :=
  Units.ext (mix_self e _)

theorem piece_mul' {e : A} (he : e * e = e) (x y : GL n A) : piece he (x * y) = piece he x * piece he y :=
  Units.ext (by
    show e • (x.1 * y.1) + (1 - e) • (1 : Matrix n n A) = (e • x.1 + (1 - e) • 1) * (e • y.1 + (1 - e) • 1)
    rw [mix_mul he, Matrix.one_mul])

theorem piece_conj {e : A} (he : e * e = e) (b x : GL n A) :
    b * piece he x * b⁻¹ = piece he (b * x * b⁻¹) := by
  apply Units.ext
  show b.1 * (e • x.1 + (1 - e) • (1 : Matrix n n A)) * (b⁻¹).1 =
    e • (b.1 * x.1 * (b⁻¹).1) + (1 - e) • (1 : Matrix n n A)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Units.mul_inv]

theorem smul_piece_sub {e : A} (he : e * e = e) (x : GL n A) :
    e • ((piece he x).1 - 1) = (piece he x).1 - 1 := by
  have h : (piece he x).1 - 1 = e • (x.1 - 1) := by
    show e • x.1 + (1 - e) • (1 : Matrix n n A) - 1 = _
    rw [smul_sub, sub_smul, one_smul]; abel
  rw [h, smul_smul, he]

theorem piece_apply {e : A} (he : e * e = e) (x : GL n A) (i j : n) :
    (piece he x).1 i j = e * x.1 i j + (1 - e) * (1 : Matrix n n A) i j := rfl

theorem map_mix {B : Type} [CommRing B] (ψ : A →+* B) (e m d : A) :
    ψ (e * m + (1 - e) * d) = ψ e * ψ m + (1 - ψ e) * ψ d := by
  simp only [map_add (f := _), map_mul, map_sub, map_one]

theorem map_one_apply {B : Type} [CommRing B] (ψ : A →+* B) (i j : n) :
    ψ ((1 : Matrix n n A) i j) = (1 : Matrix n n B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end Generic

section Stab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem piece_frGL (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) {φ : Formalism.L2.Herm.intAf F E} (hφ : φ * φ = φ)
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    piece he (frGL β y) = frGL β (piece hφ y) := by
  have h1 : intGL F E n (piece hφ y) = piece he (intGL F E n y) := by
    apply Units.ext
    ext i j
    show (((piece hφ y).1 i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) =
      (φ : E ⊗[F] Formalism.L2.Herm.Af F) * ((y.1 i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) +
        (1 - (φ : E ⊗[F] Formalism.L2.Herm.Af F)) * (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j
    rw [piece_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  show piece he (β * intGL F E n y * β⁻¹) = β * intGL F E n (piece hφ y) * β⁻¹
  rw [h1, piece_conj]

theorem piece_mem_St {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {φ : Formalism.L2.Herm.intAf F E} (hφ : φ * φ = φ)
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (hx : x ∈ St β) : piece he x ∈ St β := by
  obtain ⟨y, rfl⟩ := hx
  rw [piece_frGL β hφ he]
  exact ⟨_, rfl⟩

theorem redFn_piece {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {φ : Formalism.L2.Herm.intAf F E} (hφ : φ * φ = φ)
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (hx : x ∈ St β) (PP : Pl E) (h : resS F PP φ = 1) :
    redFn β PP (piece he x) = redFn β PP x := by
  obtain ⟨y, rfl⟩ := hx
  rw [piece_frGL β hφ he, redFn_frGL, redFn_frGL]
  apply Units.ext
  ext i j
  show resS F PP ((piece hφ y).1 i j) = resS F PP (y.1 i j)
  rw [piece_apply, map_add (f := _), map_mul, map_mul, h, map_sub, h, map_one, sub_self, zero_mul, add_zero, one_mul]

theorem redFn_piece_eq_one {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {φ : Formalism.L2.Herm.intAf F E}
    (he : (φ : E ⊗[F] Formalism.L2.Herm.Af F) * φ = φ) (hx : piece he x ∈ St β) (PP : Pl E) (h : resS F PP φ = 0) :
    redFn β PP (piece he x) = 1 :=
  redFn_eq_one β PP _ hx φ h (smul_piece_sub he x)

end Stab

section Adelic

variable {D : D7}

def phi (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : Formalism.L2.Herm.intAf D.host.F D.host.E :=
  adS D.host.F D.host.E (idemAd fun w => w = v)

theorem phi_idem (v : HeightOneSpectrum (𝓞 D.host.F)) : phi D v * phi D v = phi D v := by
  unfold phi
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases h : w = v
  · have e := idemAd_pos (F := D.host.F) (P := fun w => w = v) (v := w) h
    exact (congrArg₂ (· * ·) e e).trans ((one_mul _).trans e.symm)
  · have e := idemAd_neg (F := D.host.F) (P := fun w => w = v) (v := w) h
    exact (congrArg₂ (· * ·) e e).trans ((zero_mul _).trans e.symm)

theorem phi_idem' (v : HeightOneSpectrum (𝓞 D.host.F)) :
    (phi D v : Formalism.IndefR.Lev.EAf D) * (phi D v : Formalism.IndefR.Lev.EAf D) = (phi D v : Formalism.IndefR.Lev.EAf D) :=
  congrArg Subtype.val (phi_idem v)

theorem resS_phi_pos {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} (h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) :
    resS D.host.F PP (phi D v) = 1 :=
  resS_idemAd_pos PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl h

theorem resS_phi_neg {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)} (h : ¬ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) :
    resS D.host.F PP (phi D v) = 0 :=
  resS_idemAd_neg PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl h

def epsF (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AF D.host.F := (exists_placeIdem (D := D) v).choose

theorem epsF_spec (v : HeightOneSpectrum (𝓞 D.host.F)) : IsPlaceIdem D v (epsF D v) :=
  (exists_placeIdem (D := D) v).choose_spec

def fE (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D := algebraMap _ _ (epsF D v)

theorem fE_idem (v : HeightOneSpectrum (𝓞 D.host.F)) : fE D v * fE D v = fE D v := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  exact place_idem hΦ (epsF_spec v)

theorem fE_conj (v : HeightOneSpectrum (𝓞 D.host.F)) : cA D (fE D v) = fE D v := cA_algebraMap _

theorem finSw_fE (v : HeightOneSpectrum (𝓞 D.host.F)) : finSw D (fE D v) = (phi D v : Formalism.IndefR.Lev.EAf D) := by
  obtain ⟨α, h, h1, h0⟩ := epsF_spec (D := D) v
  have hα : α = ((idemAd (F := D.host.F) fun w => w = v : _) : _) := FiniteAdeleRing.ext _ fun w => by
    by_cases hw : w = v
    · subst hw
      exact h1.trans (idemAd_pos (F := D.host.F) (P := fun w' => w' = w) (v := w) rfl).symm
    · exact (h0 w hw).trans (idemAd_neg (F := D.host.F) (P := fun w' => w' = v) (v := w) hw).symm
  unfold fE
  rw [h, hα]
  rfl

def cmp (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) : GA D V →* GA D V where
  toFun g := ⟨piece (fE_idem v) g.1, piece_mem _ _ (fE_idem v) (fE_conj v) g.2⟩
  map_one' := Subtype.ext (piece_one (fE_idem v))
  map_mul' x y := Subtype.ext (piece_mul' (fE_idem v) x.1 y.1)

variable (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V)

theorem finE_cmp : finE V (cmp V v g) = piece (phi_idem' v) (finE V g) := by
  apply Units.ext
  ext i j
  refine (map_mix (finSw D) (fE D v) (mt V g i j) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)).trans ?_
  rw [finSw_fE, map_one_apply]
  rfl

end Adelic

section Local

variable {D : D7} {ι : Formalism.L2.DIV.AfE D.host.F D.host.E →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

variable (hι : ∀ x a, ι (x ⊗ₜ[D.host.F] a) = algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E a)
include hι

end Local

section Level

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

end Level

end GlobalTheory.LevelProduct

end
