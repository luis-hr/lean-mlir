import SSA.Projects.MLIRSem.Builtin.Types

open LeanMLIR

namespace Memref

inductive Op
  | load : Builtin.MemrefScalar -> Op
  | store : Builtin.MemrefScalar -> Op
