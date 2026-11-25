module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SpanPowMulLe
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsSubDivMemSP
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix

@[expose] public section

open NumberField Module Matrix

open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

noncomputable section

namespace Formalism.L2.SG.Pf.fibreCountingData

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

alias jK_conjO := _root_.Formalism.HermitianLattices.Ext.L3.WA.algebraMap_conjO

theorem star_mem_SP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (hF : IsFixF K F) {r : K}
    (hr : r ∈ HU.SP K 𝔭) : star r ∈ HU.SP K 𝔭 := by
  obtain ⟨t, ht, z, hz⟩ := HU.mem_SP.1 hr
  refine HU.mem_SP.2 ⟨t, ht, conjO K z, ?_⟩
  rw [jK_conjO, hz, star_mul', star_jK_ι hF, mul_comm]

theorem div_mem_SP_of_mem {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {d : 𝓞 F} (hd : d ≠ 0) {x : 𝓞 K}
    {k : ℕ} (hk : vF 𝔭 d ≤ k) (hx : x ∈ extP K 𝔭 ^ k) :
    haveI := h𝔭.isPrime; jK x / jK (ι d) ∈ HU.SP K 𝔭 :=
  (div_mem_SP_iff h𝔭 hd _).2 (Ideal.pow_le_pow_right hk hx)

end Formalism.L2.SG.Pf.fibreCountingData
