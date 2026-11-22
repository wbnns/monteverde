import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Machines.Turing.TM2.Reverse.Transfer
import CslibFrontier.Computability.Complexity.Classes.NP.Image
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Reduction.Equiv
import CslibFrontier.Computability.Complexity.Classes.Padding

/-! Probe: every cslib-frontier name that the Monteverde plan uses must resolve. -/

open Cslib.Complexity Turing Turing.MultiTapeTM

#check @P
#check @NP
#check @IsVerifier.of_padding
#check @encList
#check @encFinite
#check @encPair
#check @encBits
#check @encBool
#check @frame
#check @TM2ComputableInPolyTime.computableInPolyTime_encList
#check @TM2ComputableInPolyTime.computableInPolyTime
#check @ComputableInPolyTime.exists_tm2ComputableInPolyTime
#check @computableInPolyTime_iff_tm2
#check @trans_encList_polyTime
#check @ComputableInPolyTime.comp
#check @ComputableInPolyTime.of_eq
#check @ComputableInPolyTime.of_finite
#check @ComputableInPolyTime.prod
#check @ComputableInPolyTime.ite
#check @PolyTimeReducible.mem_P
#check @PolyTimeReducible.mem_NP
#check @PolyTimeEquiv.mem_P_iff
#check @PolyTimeEquiv.mem_NP_iff
#check @mem_P_image
#check @mem_NP_image
#check @image_SAT_mem_NP
#check @CookLevin.SAT_npComplete
#check @NPComplete.mem_P_iff
#check @mem_NP_of_witness
#check @Decoder.list
#check @Decoder.unary
#check @P_subset_NP
#check @E_eq_NE_of_P_eq_NP
#check @Turing.TM2ComputableInPolyTime
#check @Turing.FinTM2
