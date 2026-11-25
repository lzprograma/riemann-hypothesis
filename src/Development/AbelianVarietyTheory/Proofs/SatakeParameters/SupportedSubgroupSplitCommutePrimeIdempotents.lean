module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
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
import Mathlib.RingTheory.PiTensorProduct
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IdemSupport

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mix_mul {f : A} (hf : f * f = f) (a b c d : Matrix n n A) :
    (f • a + (1 - f) • b) * (f • c + (1 - f) • d) = f • (a * c) + (1 - f) • (b * d) := by
  have h1 : f * (1 - f) = 0 := by linear_combination -hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hf, h1, h2, h3, zero_smul,
    add_zero, zero_add]

omit [Fintype n] [DecidableEq n] in
theorem mix_self (f : A) (a : Matrix n n A) : f • a + (1 - f) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

theorem mix_split {f : A} (hf : f * f = f) {a b c : Matrix n n A} (hb : b = f • a + (1 - f) • (1 : Matrix n n A))
    (hc : c = (1 - f) • a + f • (1 : Matrix n n A)) : b * c = a := by
  rw [hb, hc, add_comm ((1 - f) • a), mix_mul hf, mul_one, one_mul, mix_self]

omit [Fintype n] in
theorem smul_mix {f : A} (hf : f * f = f) {a b : Matrix n n A} (hb : b = f • a + (1 - f) • (1 : Matrix n n A)) :
    (1 - f) • b = (1 - f) • (1 : Matrix n n A) := by
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  rw [hb, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, zero_add]

def piece {f : A} (hf : f * f = f) (g : GL n A) : GL n A where
  val := f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)
  inv := f • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - f) • (1 : Matrix n n A)
  val_inv := by rw [mix_mul hf, Units.mul_inv, one_mul, mix_self]
  inv_val := by rw [mix_mul hf, Units.inv_mul, one_mul, mix_self]

theorem piece_mem (σ : A →+* A) (J : Matrix n n A) {f : A} (hf : f * f = f) (hσ : σ f = f) {g : GL n A}
    (hg : g ∈ Formalism.UG.UJ σ J) : piece hf g ∈ Formalism.UG.UJ σ J := by
  have hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  change Formalism.UG.cT σ (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) * J *
    (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) = J
  have h1 : Formalism.UG.cT σ (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) =
      f • Formalism.UG.cT σ (g : Matrix n n A) + (1 - f) • Formalism.UG.cT σ (1 : Matrix n n A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ]
  rw [h1, Formalism.UG.cT_one]
  conv_lhs => rw [← mix_self f J]
  rw [mix_mul hf, mix_mul hf, hg', one_mul, mul_one, mix_self]

theorem supp_iff (f : A) (g : Matrix n n A) :
    (∀ i j, f * (g - 1) i j = (g - 1) i j) ↔ (1 - f) • g = (1 - f) • (1 : Matrix n n A) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linear_combination -h

theorem commute_of_supp {f f' : A} (h : f * f' = 0) {g g' : Matrix n n A}
    (hg : ∀ i j, f * (g - 1) i j = (g - 1) i j) (hg' : ∀ i j, f' * (g' - 1) i j = (g' - 1) i j) :
    g * g' = g' * g := by
  have e1 : f • (g - 1) = g - 1 := Matrix.ext hg
  have e2 : f' • (g' - 1) = g' - 1 := Matrix.ext hg'
  have e3 : (g - 1) * (g' - 1) = 0 := by
    rw [← e1, ← e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, zero_smul]
  have e4 : (g' - 1) * (g - 1) = 0 := by
    rw [← e1, ← e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm f' f, h, zero_smul]
  have : g * g' - g' * g = (g - 1) * (g' - 1) - (g' - 1) * (g - 1) := by noncomm_ring
  rw [← sub_eq_zero, this, e3, e4, sub_zero]

end Generic

variable {D : D7}

theorem mt_mul (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one, Units.val_one]

theorem mt_inj (V : HSp D) {g h : GA D V} (e : mt V g = mt V h) : g = h :=
  Subtype.ext (Units.ext e)

theorem suppF_iff (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    SuppF V f g ↔ (1 - f) • mt V g = (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
  supp_iff f _

def suppGroup (V : HSp D) (f : Formalism.L2.Theta.AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  one_mem' := by
    change SuppF V f 1
    rw [suppF_iff, mt_one]
  mul_mem' := by
    intro a b ha hb
    change SuppF V f _ at ha hb ⊢
    rw [suppF_iff] at ha hb ⊢
    rw [mt_mul, ← Matrix.smul_mul, ha, Matrix.smul_mul, one_mul, hb]
  inv_mem' := by
    intro a ha
    change SuppF V f _ at ha ⊢
    rw [suppF_iff] at ha ⊢
    have h := congrArg (· * mt V a⁻¹) ha
    simp only [Matrix.smul_mul, one_mul] at h
    rw [← h, ← mt_mul, mul_inv_cancel, mt_one]

theorem exists_piece (V : HSp D) {f : Formalism.L2.Theta.AE D} (hf : f * f = f) (hc : cA D f = f) (g : GA D V) :
    ∃ g₁ : GA D V, mt V g₁ = f • mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
  ⟨⟨piece hf g.1, piece_mem _ _ hf hc g.2⟩, rfl⟩

theorem exists_split (V : HSp D) {f : Formalism.L2.Theta.AE D} (hf : f * f = f) (hc : cA D f = f) (g : GA D V) :
    ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂ := by
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  obtain ⟨g₁, e₁⟩ := exists_piece V hf hc g
  obtain ⟨g₂, e₂⟩ := exists_piece V h3 (by rw [map_sub, map_one, hc]) g
  have s₁ := (suppF_iff V f g₁).2 (smul_mix hf e₁)
  have s₂ := (suppF_iff V (1 - f) g₂).2 (smul_mix h3 e₂)
  rw [sub_sub_cancel] at e₂
  have e4 := mix_split hf e₁ e₂
  have e5 := mt_mul V g₁ g₂
  exact ⟨g₁, g₂, s₁, s₂, mt_inj V (e5.trans e4).symm⟩

theorem commute_of_suppF (V : HSp D) {f f' : Formalism.L2.Theta.AE D} {g g' : GA D V} (h : f * f' = 0)
    (hg : SuppF V f g) (hg' : SuppF V f' g') : Commute g g' := by
  have h1 : mt V g * mt V g' = mt V g' * mt V g := commute_of_supp h hg hg'
  rw [← mt_mul, ← mt_mul] at h1
  exact (commute_iff_eq g g').2 (mt_inj V h1)

theorem mem_GfC_of_suppF (V : HSp D) {f : Formalism.L2.Theta.AE D} (hf : infPart D f = 0) {g : GA D V}
    (hg : SuppF V f g) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := congrArg (infPart D) (hg i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

structure Comp (D : D7) (Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) : Prop where
  ext : ∀ z, infPart D z = 0 → Φ z = 0 → z = 0
  surj : ∀ s, ∃ z, infPart D z = 0 ∧ Φ z = s
  inc : ∀ x, Φ (incA D x) = algebraMap _ _ x
  int : ∀ z, finPart D z ∈ intAE D ↔ ∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E
  base : ∀ (a : AF D.host.F) Q, Φ (algebraMap _ _ a) Q =
    GlobalTheory.AdeleBaseChange.locMap D.host.F Q (a.2 (Q.under (𝓞 D.host.F)))

private theorem isCMExt_of (D : D7) :
    HeckeCharacterZeroLocus.ThmBIn.IsCMExt D.host.F D.host.E D.sp.cm.sig :=
  ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩

private theorem Comp.toCM {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΦ : Comp D Φ) : GlobalTheory.CMPrimeIdele.Comp Φ :=
  ⟨hΦ.ext, hΦ.surj, hΦ.inc, hΦ.int, hΦ.base⟩

theorem mem_intAE_iff (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ intAE D ↔ Formalism.IndefR.Lev.swapAE D z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E :=
  GlobalTheory.CMPrimeIdele.mem_intAE_iff z

theorem exists_comp (D : D7) : ∃ Φ, Comp D Φ := by
  obtain ⟨Φ, h1, h2, h3, h4, h5⟩ := GlobalTheory.CMPrimeIdele.exists_comp D.host.F D.host.E
  exact ⟨Φ, h1, h2, h3, h4, h5⟩

def IsDelta (Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) : Prop :=
  infPart D e = 0 ∧ Φ e P = 1 ∧ ∀ Q, Q ≠ P → Φ e Q = 0

def Comparison₂ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) : Prop :=
  ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)

def cO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)

theorem cO_coe (x : 𝓞 D.host.E) : (cO D x : D.host.E) = star (x : D.host.E) := rfl

theorem cO_cO (x : 𝓞 D.host.E) : cO D (cO D x) = x :=
  GlobalTheory.CMPrimeIdele.cO_cO (isCMExt_of D) x

def cP (P : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) :=
  HeightOneSpectrum.comap (cO D).toRingHom (cO D).surjective P

theorem mem_cP (P : HeightOneSpectrum (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (cP P).asIdeal ↔ cO D x ∈ P.asIdeal := Iff.rfl

theorem eq_of_le {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : P.asIdeal ≤ Q.asIdeal) : P = Q :=
  GlobalTheory.CMPrimeIdele.eq_of_le h

theorem isConjPl_iff (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = cP P := by
  constructor
  · intro h
    refine (eq_of_le fun x hx => ?_).symm
    obtain ⟨c, hc, e⟩ := h _ ((mem_cP P x).1 hx)
    have : c = x := by
      apply RingOfIntegers.ext
      rw [e, cO_coe, star_star]
    exact this ▸ hc
  · rintro rfl c hc
    exact ⟨cO D c, by rw [mem_cP, cO_cO]; exact hc, rfl⟩

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem cA_algebraMap (a : AF D.host.F) :
    cA D (algebraMap _ (Formalism.L2.Theta.AE D) a) = algebraMap _ (Formalism.L2.Theta.AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = a ⊗ₜ[D.host.F] 1
  rw [map_one]

theorem parts_cA (z : Formalism.L2.Theta.AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) ∧
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) :=
  GlobalTheory.CMPrimeIdele.parts_cA z

theorem finPart_cA_mem {z : Formalism.L2.Theta.AE D} (hz : finPart D z ∈ intAE D) : finPart D (cA D z) ∈ intAE D :=
  GlobalTheory.CMPrimeIdele.finPart_cA_mem hz

theorem Comparison₂.conj {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : Comparison₂ P e) :
    Comparison₂ (cP P) (cA D e) :=
  GlobalTheory.CMPrimeIdele.Comparison₂.conj (isCMExt_of D) h

theorem inv_mem_iff (Q : HeightOneSpectrum (𝓞 D.host.E)) {x : 𝓞 D.host.E} (hx : x ≠ 0) :
    algebraMap D.host.E (Q.adicCompletion D.host.E) ((x : D.host.E)⁻¹) ∈ Q.adicCompletionIntegers D.host.E ↔
      x ∉ Q.asIdeal :=
  GlobalTheory.CMPrimeIdele.inv_mem_iff Q hx

section

variable {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

theorem ev_mul (a b : Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a * b) Q = Φ a Q * Φ b Q := by rw [map_mul]; rfl

theorem ev_add (a b : Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a + b) Q = Φ a Q + Φ b Q := by rw [map_add (f := _)]; rfl

theorem ev_zero (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 0 Q = 0 := by rw [map_zero]; rfl

variable (hΦ : Comp D Φ)
include hΦ

theorem Comp.ext' {a b : Formalism.L2.Theta.AE D} (h1 : infPart D a = infPart D b) (h2 : ∀ Q, Φ a Q = Φ b Q) : a = b :=
  GlobalTheory.CMPrimeIdele.Comp.ext' hΦ.toCM h1 h2

theorem exists_delta (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ e, IsDelta Φ P e :=
  GlobalTheory.CMPrimeIdele.exists_delta hΦ.toCM P

theorem delta_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : IsDelta Φ P e)
    (h' : IsDelta Φ P e') : e = e' :=
  GlobalTheory.CMPrimeIdele.delta_unique hΦ.toCM h h'

theorem delta_idem {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : IsDelta Φ P e) :
    e * e = e :=
  GlobalTheory.CMPrimeIdele.delta_idem hΦ.toCM h

theorem not_int_iff {e : Formalism.L2.Theta.AE D} (he : e * e = e) {x : 𝓞 D.host.E} (hx : x ≠ 0) :
    finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D ↔ ∃ Q, Φ e Q ≠ 0 ∧ x ∈ Q.asIdeal :=
  GlobalTheory.CMPrimeIdele.not_int_iff hΦ.toCM he hx

theorem tie_iff {e : Formalism.L2.Theta.AE D} (he : e * e = e) (h0 : infPart D e = 0)
    (P : HeightOneSpectrum (𝓞 D.host.E)) : Comparison₂ P e ↔ IsDelta Φ P e :=
  GlobalTheory.CMPrimeIdele.tie_iff hΦ.toCM he h0 P

theorem delta_conj {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : IsDelta Φ P e) :
    IsDelta Φ (cP P) (cA D e) :=
  GlobalTheory.CMPrimeIdele.delta_conj hΦ.toCM (isCMExt_of D) h

theorem place_comp {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap _ (Formalism.L2.Theta.AE D) ε) = 0 ∧
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v → Φ (algebraMap _ _ ε) Q = 1) ∧
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ≠ v → Φ (algebraMap _ _ ε) Q = 0) :=
  GlobalTheory.CMPrimeIdele.place_comp hΦ.toCM h

end

theorem under_cP (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (cP P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) :=
  GlobalTheory.CMPrimeIdele.under_cP (isCMExt_of D) P

theorem eq_or_eq_cP {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) : Q = P ∨ Q = cP P :=
  GlobalTheory.CMPrimeIdele.eq_or_eq_cP (isCMExt_of D) h

theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε :=
  GlobalTheory.CMPrimeIdele.exists_placeIdem v

theorem placeIdem_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨β, rfl, k1, k0⟩ := h'
  congr 1
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases hw : w = v
  · subst hw; exact h1.trans k1.symm
  · exact (h0 w hw).trans (k0 w hw).symm

section

variable {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
include hΦ

theorem place_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap _ (Formalism.L2.Theta.AE D) ε * algebraMap _ _ ε = algebraMap _ _ ε := by
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ h
  refine hΦ.ext' (by rw [RingHom.map_mul, h0, zero_mul]) fun Q => ?_
  rw [ev_mul]
  by_cases hQ : Q.under (𝓞 D.host.F) = v
  · rw [h1 Q hQ, one_mul]
  · rw [h2 Q hQ, zero_mul]

theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') :
    algebraMap _ (Formalism.L2.Theta.AE D) ε * algebraMap _ _ ε' = 0 := by
  obtain ⟨h0, -, h2⟩ := place_comp hΦ h
  obtain ⟨-, -, k2⟩ := place_comp hΦ h'
  refine hΦ.ext' (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero]) fun Q => ?_
  rw [ev_mul, ev_zero]
  by_cases hQ : Q.under (𝓞 D.host.F) = v
  · rw [k2 Q (hQ ▸ hv), mul_zero]
  · rw [h2 Q hQ, zero_mul]

theorem delta_of_isIdemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : IsIdemAt e P) :
    IsDelta Φ P e := by
  obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
  refine (tie_iff hΦ h1 ?_ P).1 ht
  have : e = (e + cA D e) * e := by linear_combination -h1 - h2
  rw [this, h3, RingHom.map_mul, (place_comp hΦ hε).1, zero_mul]

theorem of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f) :
    IsDelta Φ P e ∧ ∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧ f = algebraMap _ _ ε := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have hd := delta_of_isIdemAt hΦ h
    obtain ⟨⟨-, h2, v, ε, hε, h3⟩, -⟩ := h
    refine ⟨hd, ε, ?_, h3⟩
    have h4 : Φ (cA D e) P = 0 := by
      have := ev_mul (Φ := Φ) e (cA D e) P
      rwa [h2, ev_zero, hd.2.1, one_mul, eq_comm] at this
    have h5 : P.under (𝓞 D.host.F) = v := by
      by_contra hv
      have := (place_comp hΦ hε).2.2 P hv
      rw [← h3, ev_add, h4, hd.2.1, add_zero] at this
      exact one_ne_zero this
    exact h5 ▸ hε
  · have hd := (tie_iff hΦ (place_idem hΦ hε) (place_comp hΦ hε).1 P).1 ht
    refine ⟨hd, ε, ?_, rfl⟩
    have h5 : P.under (𝓞 D.host.F) = v := by
      by_contra hv
      exact one_ne_zero (hd.2.1.symm.trans ((place_comp hΦ hε).2.2 P hv))
    exact h5 ▸ hε

theorem exists_isPrimeIdem (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ e f, IsPrimeIdem P e f := by
  obtain ⟨e, f, -, h⟩ := GlobalTheory.CMPrimeIdele.exists_isPrimeIdem_of_comp hΦ.toCM (isCMExt_of D) P
  exact ⟨e, f, h⟩

end

theorem supported_group_and_prime_idempotents : ∀ {D : D7} (V : HSp D), (∀ f : Formalism.L2.Theta.AE D, f * f = f → cA D f = f → (∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g) ∧ (∀ g : GA D V, ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂) ∧ ∀ f' g g', f * f' = 0 → SuppF V f g → SuppF V f' g' → Commute g g') ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → f * f = f ∧ cA D f = f ∧ (∀ g, SuppF V f g → g ∈ GfC V) ∧ (∀ e' f', IsPrimeIdem P e' f' → e' = e ∧ f' = f) ∧ ∀ P' e' f', IsPrimeIdem P' e' f' → f * f' = 0 ∨ (f' = f ∧ (P' = P ∨ Formalism.IndefR.Lev.IsConjPl P P'))) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) P' e, IsIdemAt e P → Formalism.IndefR.Lev.IsConjPl P P' → IsIdemAt (cA D e) P' := by
  intro D V
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  refine ⟨fun f hf hc => ⟨⟨suppGroup V f, fun _ => Iff.rfl⟩, exists_split V hf hc,
    fun f' g g' h hg hg' => commute_of_suppF V h hg hg'⟩, exists_isPrimeIdem hΦ, fun P e f h => ?_,
    fun P P' e h hc => ?_⟩
  · obtain ⟨hd, ε, hε, rfl⟩ := of_isPrimeIdem hΦ h
    refine ⟨place_idem hΦ hε, cA_algebraMap ε, fun g hg => mem_GfC_of_suppF V (place_comp hΦ hε).1 hg,
      fun e' f' h' => ?_, fun P' e' f' h' => ?_⟩
    · obtain ⟨hd', ε', hε', rfl⟩ := of_isPrimeIdem hΦ h'
      exact ⟨delta_unique hΦ hd' hd, by rw [placeIdem_unique hε' hε]⟩
    · obtain ⟨-, ε', hε', rfl⟩ := of_isPrimeIdem hΦ h'
      by_cases hv : P'.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
      · rw [hv] at hε'
        exact Or.inr ⟨by rw [placeIdem_unique hε' hε], (eq_or_eq_cP hv).imp id (isConjPl_iff P P').2⟩
      · exact Or.inl (place_orth hΦ hε hε' (Ne.symm hv))
  · rw [(isConjPl_iff P P').1 hc]
    obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
    exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩,
      Comparison₂.conj ht⟩

end GlobalTheory.IdemSupport
