from dataclasses import dataclass

class AstNode:
  line: int
  column: int
  def copy_meta(self, source):
    self.line = source.line
    self.column = source.column

@dataclass
class Number(AstNode):
  value: int

@dataclass
class String(AstNode):
  value: str

@dataclass
class Const(AstNode):
  name: str

@dataclass
class FuncCall(AstNode):
  func: AstNode
  args: list[AstNode]

@dataclass
class Ident(AstNode):
  name: str

@dataclass
class Op(AstNode):
  name: str

@dataclass
class GetAttr(AstNode):
  lhs: AstNode
  rhs: str

@dataclass
class Assign(AstNode):
  lhs: AstNode
  rhs: AstNode

@dataclass
class Block(AstNode):
  entries: list[AstNode]

@dataclass
class TopLevel(AstNode):
  body: Block

@dataclass
class Type(AstNode):
  base: AstNode

@dataclass
class SymTabEntry:  # Not AstNode
  type: Type
  ref_node: AstNode  # For error reporting
  is_func_param: bool = False
  is_declared_local: bool = False
  is_upval: bool = False
  is_global: bool = False
  is_pending_nonlocal: bool = False

upval_binding_counter = 0
class UpvalBindings:  # Not AstNode
  def __init__(self, to_bind, func_name):
    self.to_bind = to_bind  # map of ident to ste's to bind
    self.struct_name = '$Upvals_' + func_name
    global upval_binding_counter
    self.parent_binding_name = '$uv' + str(upval_binding_counter)
    upval_binding_counter += 1

@dataclass
class FuncDef(AstNode):
  rtype: AstNode
  name: str
  params: list[AstNode]
  body: Block
  # True when hoisted out of another function, and so shouldn't be visible in
  # the namespace to which it was moved.
  hidden: bool = False

  def __post_init__(self):
    self.symtab = {}  # values are SymTabEntry
    self.upval_bindings = {}  # names are funcname, values are UpvalBindings

@dataclass
class FuncType(Type):
  rtype: AstNode
  params: list[AstNode]

@dataclass
class SliceDecl(Type):
  pass

@dataclass
class FixedArrayDecl(Type):
  size: AstNode

@dataclass
class PointerDecl(Type):
  pass

@dataclass
class MacroCallWithBlock(AstNode):
  func: FuncCall
  body: Block

@dataclass
class Return(AstNode):
  value: AstNode

@dataclass
class Pass(AstNode):
  pass

@dataclass
class Nonlocal(AstNode):
  vars: list[str]

@dataclass
class For(AstNode):
  it: AstNode
  collection: AstNode
  body: Block
  els: Block

@dataclass
class Elif(AstNode):
  cond: AstNode
  body: Block

@dataclass
class If(AstNode):
  cond: AstNode
  body: Block
  elifs: list[Elif]
  els: Block

@dataclass
class TypedVar(AstNode):
  type: Type
  name: str

@dataclass
class VarDecl(AstNode):
  type: AstNode
  name: str
  init: AstNode

@dataclass
class UnaryExpr(AstNode):
  op: AstNode
  obj: AstNode

@dataclass
class Expr(AstNode):
  # 3 + 2n long:
  #   VAL0 op0 VAL1 [op1 VAL2 ...]
  chain: list[AstNode]

@dataclass
class CompExpr(AstNode):
  # 3 + 2n long:
  #   VAL0 cmp0 VAL1 [cmp1 VAL2 ...]
  # for x < y < z
  # === x < y and y < z, but y only eval once.
  chain: list[AstNode]

@dataclass
class PackageReference(AstNode):
  lhs: AstNode
  rhs: AstNode

@dataclass
class GetItem(AstNode):
  obj: AstNode
  index: AstNode

@dataclass
class Struct(AstNode):
  name: str
  members: list[Type]

@dataclass
class Union(AstNode):
  name: str
  members: list[Type]

@dataclass
class ParseError:
  line: int
  column: int
  got: AstNode
