from dataclasses import dataclass

class AstNode:
  line: int
  column: int

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
class FuncDef(AstNode):
  rtype: AstNode
  name: str
  params: list[AstNode]
  body: Block

  def __post_init__(self):
    self.symtab = {}

@dataclass
class Type(AstNode):
  base: AstNode

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
class BinaryExpr(AstNode):
  lhs: AstNode
  rhs: AstNode
  op: AstNode

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
