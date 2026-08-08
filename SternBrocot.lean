-- Core — the construction, ℝ-free
import SternBrocot.Core.Basic
import SternBrocot.Core.Tail
import SternBrocot.Core.Order
import SternBrocot.Core.Completeness
import SternBrocot.Core.Node
import SternBrocot.Core.Enumeration
import SternBrocot.Core.PathOrder
import SternBrocot.Core.Bridge
import SternBrocot.Core.Density
import SternBrocot.Core.Signed
import SternBrocot.Core.SignedOrder
import SternBrocot.Core.Magnitude
import SternBrocot.Core.Induction
import SternBrocot.Core.Gosper
import SternBrocot.Core.GosperRat
import SternBrocot.Core.IntrinsicCore

-- Real — the map to ℝ
import SternBrocot.Real.ToReal
import SternBrocot.Real.SignedToReal
import SternBrocot.Real.Field
import SternBrocot.Real.IntrinsicAgreement
import SternBrocot.Real.Complete

-- CF — the continued-fraction library
import SternBrocot.CF.Degree
import SternBrocot.CF.Shift
import SternBrocot.CF.Lagrange
import SternBrocot.CF.Convergent
import SternBrocot.CF.Hurwitz
import SternBrocot.CF.Reduction
import SternBrocot.CF.Legendre

-- Machine-checked checks that the definitions mean what is claimed
import SternBrocot.Examples
