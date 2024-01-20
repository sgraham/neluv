from dataclasses import dataclass

class Location:
  line: int
  column: int

@dataclass
class Number(Location):
  value: int

@dataclass
class String(Location):
  value: str

@dataclass
class Const(Location):
  name: str

@dataclass
class FuncCall(Location):
  func: object
  args: list[object]

@dataclass
class Ident(Location):
  name: object

@dataclass
class Op(Location):
  name: str

@dataclass
class GetAttr(Location):
  lhs: object
  rhs: str

@dataclass
class Assign(Location):
  lhs: object
  rhs: object

@dataclass
class Block(Location):
  entries: list[object]

@dataclass
class TopLevel(Location):
  body: Block

@dataclass
class FuncDef(Location):
  rtype: object
  name: str
  params: list[object]
  body: Block

@dataclass
class Type(Location):
  base: object

@dataclass
class FuncType(Type):
  rtype: object
  params: list[object]

@dataclass
class SliceDecl(Type):
  pass

@dataclass
class FixedArrayDecl(Type):
  size: object

@dataclass
class PointerDecl(Type):
  pass

@dataclass
class MacroCallWithBlock(Location):
  func: FuncCall
  body: Block

@dataclass
class Return(Location):
  value: object

@dataclass
class Pass(Location):
  pass

@dataclass
class For(Location):
  it: object
  collection: object
  body: Block
  els: Block

@dataclass
class Elif(Location):
  cond: object
  body: Block

@dataclass
class If(Location):
  cond: object
  body: Block
  elifs: list[Elif]
  els: Block

@dataclass
class TypedVar(Location):
  type: Type
  name: str

@dataclass
class VarDecl(Location):
  type: object
  name: str
  init: object

@dataclass
class UnaryExpr(Location):
  op: object
  obj: object

@dataclass
class BinaryExpr(Location):
  lhs: object
  rhs: object
  op: object

@dataclass
class CompExpr(Location):
  # 3 + 2n long:
  #   VAL0 cmp0 VAL1 [cmp1 VAL2 ...]
  # for x < y < z
  # === x < y and y < z, but y only eval once.
  chain: list[object]

@dataclass
class PackageReference(Location):
  lhs: object
  rhs: object

@dataclass
class GetItem(Location):
  obj: object
  index: object

@dataclass
class Struct(Location):
  name: str
  members: list[Type]

@dataclass
class Union(Location):
  name: str
  members: list[Type]

@dataclass
class ParseError(Location):
  line: int
  column: int
  got: object
