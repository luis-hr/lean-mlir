import SSA.Projects.MLIRSem.Vector.Basic
open Builtin
namespace Vector

@[simp, reducible]
def Op.sig : Op -> List Ty
  | .reduce length t true .add =>
    [.shaped (.vector [length]) t, .shaped .scalar t]
  | .reduce length t false .add =>
    [.shaped (.vector [length]) t ]
  | .reduce length t true .mul =>
    [.shaped (.vector [length]) t]
  | .reduce length t false .mul => [.shaped (.vector [length]) t]

def Op.outTy : Op -> Ty
  | .reduce _ t _ _ => .shaped .scalar t
