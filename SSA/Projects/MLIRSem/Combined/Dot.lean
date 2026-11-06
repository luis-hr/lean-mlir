
import SSA.Projects.MLIRSem.Combined.Syntax

namespace MLIRSem
open Builtin LeanMLIR

private abbrev i32   : Ty := .shaped .scalar (.int (.int 32))
private abbrev v4i32 : Ty := .shaped (.vector [4]) (.int (.int 32))

def dotRed := [mlirsem_com| {
  ^entry(%a : !"vector<4xi32>", %b : !"vector<4xi32>"):
    %p = "arith.muli"(%a, %b) : (!"vector<4xi32>", !"vector<4xi32>") -> !"vector<4xi32>"
    %r = "vector.reduction"(%p) <{kind = #vector.kind<add>}> : (!"vector<4xi32>") -> i32
    "func.return"(%r) : (i32) -> ()
  }]

def dotLoop := [mlirsem_com| {
  ^entry(%a : !"vector<4xi32>", %b : !"vector<4xi32>"):
    %lb   = "arith.constant"() <{value = 0 : index}> : () -> index
    %ub   = "arith.constant"() <{value = 4 : index}> : () -> index
    %step   = "arith.constant"() <{value = 1 : index}> : () -> index
    %init = "arith.constant"() <{value = 0 : i32}> : () -> i32
    %r = "scf.for"(%lb, %ub, %step, %init, %a, %b) ({
      ^bb0(%i : index, %acc : i32, %a_ : !"vector<4xi32>", %b_ : !"vector<4xi32>"):
        %x = "vector.extract"(%a_, %i) : (!"vector<4xi32>", index) -> i32
        %y = "vector.extract"(%b_, %i) : (!"vector<4xi32>", index) -> i32
        %p = "arith.muli"(%x, %y) : (i32, i32) -> i32
        %s = "arith.addi"(%acc, %p) : (i32, i32) -> i32
        "scf.yield"(%s) : (i32) -> ()
    }) : (index, index, index, i32, !"vector<4xi32>", !"vector<4xi32>") -> i32
    "func.return"(%r) : (i32) -> ()
  }]

private def vec (f : Nat → Int) : TyDenote.toType v4i32 :=
  fun j => PoisonOr.value (BitVec.ofInt 32 (f j.val))

def dotIn (a b : Nat → Int) : Ctxt.Valuation (Ctxt.ofList [v4i32, v4i32]) :=
  Ctxt.Valuation.ofHVector [vec b, vec a]ₕ

-- a = [1,2,3,4], b = [5,6,7,8]:  5 + 12 + 21 + 32 = 70
#eval dotRed.denote  (dotIn (· + 1) (· + 5))     -- expect ok [70]
#eval dotLoop.denote (dotIn (· + 1) (· + 5))     -- expect ok [70]


end MLIRSem
