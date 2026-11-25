module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HeckeLocalProduct.Kernel
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host RestrictedProduct

namespace PI.HeckeProdW

variable {L : Type} [Field L] [NumberField L]

def pv (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* v.adicCompletion L where
  toFun a := (a : AdeleRing (𝓞 L) L).2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def pw (w : InfinitePlace L) : Ideles L →* w.Completion where
  toFun a := (a : AdeleRing (𝓞 L) L).1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem f_inv_mul {M : Type*} [Monoid M] (f : Ideles L →* M) (A D : Ideles L) (h : f A = f D) :
    f (A⁻¹ * D) = 1 := by
  rw [map_mul, ← h, ← map_mul, inv_mul_cancel, map_one]

theorem f_inv_mul' {M : Type*} [Monoid M] (f : Ideles L →* M) (A D : Ideles L) (h : f A = 1) :
    f (A⁻¹ * D) = f D := by
  have h1 : f A⁻¹ = 1 := by
    calc f A⁻¹ = f A⁻¹ * f A := by rw [h, mul_one]
      _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul, h1, one_mul]

theorem Phi_single [DecidableEq (HeightOneSpectrum (𝓞 L))] (v : HeightOneSpectrum (𝓞 L))
    (w : (v.adicCompletionIntegers L)ˣ) :
    Phi L (Pi.mulSingle v w) = localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w) := by
  refine Units.ext (Prod.ext rfl (Subtype.ext (funext fun v' => ?_)))
  change (((Pi.mulSingle v w : Pu L) v' : v'.adicCompletionIntegers L) : v'.adicCompletion L) = pv v' (localIdele L v (Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom w))
  by_cases h : v' = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (localIdele_snd_self L v' (Units.map (v'.adicCompletionIntegers L).subtype.toMonoidHom w)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact ((localIdele_isSupportedAt L v _).2 v' h).symm

theorem chi_unit (χ : HChar L) (u : Ideles L) (h1 : (u : AdeleRing (𝓞 L) L).1 = 1)
    (h2 : ∀ v, Valued.v ((u : AdeleRing (𝓞 L) L).2 v) = 1)
    (h3 : ∀ v, (u : AdeleRing (𝓞 L) L).2 v ≠ 1 → χ.UnrAt v) : χ.1 u = 1 := by
  classical
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring χ
  have hmemO : ∀ v : HeightOneSpectrum (𝓞 L), (u : AdeleRing (𝓞 L) L).2 v ∈ v.adicCompletionIntegers L := fun v => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact (h2 v).le
  have hunit : ∀ v : HeightOneSpectrum (𝓞 L), IsUnit (⟨_, hmemO v⟩ : v.adicCompletionIntegers L) := fun v =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 (h2 v)
  let y : Pu L := fun v => (hunit v).unit
  have hu : u = Phi L y := Units.ext (Prod.ext (h1.trans rfl) (Subtype.ext (funext fun v => rfl)))
  set p : Pu L := ∏ v ∈ T, Pi.mulSingle v (y v) with hp
  have hpv : ∀ v ∈ T, p v = y v := fun v hv => by
    rw [hp, Finset.prod_apply, Finset.prod_pi_mulSingle, ite_eq_left hv]
  have hsplit : y = p * (p⁻¹ * y) := by rw [mul_inv_cancel_left]
  have hrest : χ.1 (Phi L (p⁻¹ * y)) = 1 :=
    hT _ fun v hv => by rw [Pi.mul_apply, Pi.inv_apply, hpv v hv, inv_mul_cancel]
  rw [hu, hsplit, map_mul, map_mul, hrest, mul_one, hp, map_prod, map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Phi_single]
  by_cases hv : χ.UnrAt v
  · exact hv _ (h2 v)
  · have hv1 : (u : AdeleRing (𝓞 L) L).2 v = 1 := by
      by_contra h
      exact hv (h3 v h)
    have hx : Units.map (v.adicCompletionIntegers L).subtype.toMonoidHom (y v) = 1 := Units.ext hv1
    rw [hx, map_one, map_one]

theorem pw_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    pw w (localIdele L v x) = 1 :=
  (localIdele_isSupportedAt L v x).1 w

theorem pv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    pv v (localIdele L v x) = x := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v
    (x : v.adicCompletion L)) v = x
  simp

theorem pv_local_ne (v v' : HeightOneSpectrum (𝓞 L)) (h : v' ≠ v) (x : (v.adicCompletion L)ˣ) :
    pv v' (localIdele L v x) = 1 := by
  classical
  show (RestrictedProduct.mulSingle (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletionIntegers L) v
    (x : v.adicCompletion L)) v' = 1
  simp [h]

theorem infDiag_eq (k : Lˣ) : (infDiag k : Ideles L) = ∏ w : InfinitePlace L, infIdele L w (atInf w k) := by
  rw [infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem pw_infDiag (w : InfinitePlace L) (k : Lˣ) : pw w (infDiag k) = (atInf w k : w.Completion) := by
  rw [infDiag_eq, map_prod, Finset.prod_eq_single w]
  · exact infIdele_fst_self L w _
  · intro b _ hb
    exact infIdele_fst_ne L b w (Ne.symm hb) _
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem pv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : pv v (infDiag k) = 1 := by
  rw [infDiag_eq, map_prod]
  exact Finset.prod_eq_one fun w _ => infIdele_snd L w (atInf w k) v

theorem pw_diag (w : InfinitePlace L) (k : Lˣ) : pw w (diagUnits L k) = (atInf w k : w.Completion) := rfl

theorem pv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : pv v (diagUnits L k) = (atFin v k : v.adicCompletion L) := rfl

theorem valued_atFin (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) :
    Valued.v ((atFin v k : (v.adicCompletion L)ˣ) : v.adicCompletion L) = v.valuation L (k : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : L)

theorem locK_eq (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.UnrAt v) (k : Lˣ) :
    χ.locK v k = χ.val v ^ ordF v k := by
  apply _root_.GlobalTheory.HeckeProduct.locK_unr <;> assumption

theorem productRule (χ : HChar L) : χ.ProductRule := by
  apply _root_.GlobalTheory.HeckeProduct.hchar_productRule <;> assumption

end PI.HeckeProdW
