import Monteverde.Encoding.BlockEnc
import Monteverde.Encoding.Pair
import Monteverde.Encoding.Certificate
import Monteverde.Function.Finitize
import Monteverde.Function.Forward
import Monteverde.Function.Recoder
import Monteverde.Function.Decoder
import Monteverde.Function.Reverse
import Monteverde.Function.Bridge
import Monteverde.Classes.P
import Monteverde.Classes.NP
import Monteverde.Classes.Reduction
import Monteverde.Statements.Defs
import Monteverde.Statements.Bits
import Monteverde.Statements.Clay
import Monteverde.Statements.NegativeBranch

/-!
# Monteverde

Monteverde proves in Lean that the LeanMillenniumPrizeProblems formulation of the Clay P vs NP
statement is equivalent to P vs NP in cslib-frontier. See `README.md` for the claim, the layers
of the proof and the audit files.
-/
